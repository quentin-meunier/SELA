#!/usr/bin/python

# Copyright (C) 2019, Sorbonne Universite, LIP6
# This file is part of the SELA project, under the GPL v3.0 license
# See https://www.gnu.org/licenses/gpl-3.0.en.html for license information
# SPDX-License-Identifier: GPL-3.0-only
# Author(s): Quentin L. Meunier

from __future__ import print_function
from node import *
from config import *

import sys
import os
import re



class Graph:

    gid = 0

    def __init__(self, exp, nodeList = None):
        self.exp = exp
        self.gid = Graph.gid
        Graph.gid += 1

        self.symb2node = {}
        self.cst2node = {}
        self.nodes = set()
        self.secretNodes = set()
        self.maskNodes = set()
        self.nodeNum = 0
        self.roots = None
        if nodeList != None:
            self.roots = []
            for node in nodeList:
                n = self.copyNodeRec(node)
                self.roots.append(n)


    def copyNodeRec(self, node):
        l = []
        for child in node.children:
            n = self.copyNodeRec(child)
            l.append(n)
        if isinstance(node, SymbNode):
            n = self.makeSymbNode(node.symb, node.symbType, node.width)
            return n
        elif isinstance(node, OpNode):
            n = self.makeOpNode(node.op, l)
            return n
        elif isinstance(node, ConstNode):
            n = self.makeConstNode(node.cst, node.width)
            return n



    @staticmethod
    def loadGraph(filename):
        if not os.path.isfile(filename):
            print('*** Error: file %s does not exist.\n' % filename)
            sys.exit(1)

        g = Graph(None)
        g.gid = None
        nodePat = 'G([0-9]+)N([0-9]+)'
        nodeDefPattern = re.compile(' +%s \[shape=record, label="\{([a-zA-Z0-9: ^\\\\|&~+\-_\(\)]+)\}"\];' % (nodePat))
        transPattern = re.compile(' +%s -> %s' % (nodePat, nodePat))
        opPattern = re.compile('Op: ([\|&^+\\\\-~])+')
        constPattern = re.compile('Const: ([0-9]+)')
        maskPattern = re.compile('Symbol: ([a-zA-Z0-9_]+) \(mask\)')
        secretPattern = re.compile('Symbol: ([a-zA-Z0-9_]+)')
        nodeNum2Node = {}

        lines = open(filename, 'r')
        for line in lines:
            res = nodeDefPattern.match(line)
            if res:
                gid = int(res.group(1))
                if g.gid == None:
                    g.gid = gid
                assert(g.gid == gid)

                nodeNum = int(res.group(2))
                label = res.group(3)
                res = constPattern.match(label)
                if res:
                    cst = int(res.group(1))
                    node = g.makeConstNode(cst)
                    node.num = nodeNum
                    nodeNum2Node[nodeNum] = node
                    continue
                res = opPattern.match(label)
                if res:
                    op = res.group(1)
                    node = g.makeOpNodeNoChildren(op)
                    node.num = nodeNum
                    nodeNum2Node[nodeNum] = node
                    continue
                res = maskPattern.match(label)
                if res:
                    symb = res.group(1)
                    node = g.makeSymbNode(symb, True)
                    node.num = nodeNum
                    nodeNum2Node[nodeNum] = node
                    continue
                res = secretPattern.match(label)
                if res:
                    symb = res.group(1)
                    node = g.makeSymbNode(symb, False)
                    node.num = nodeNum
                    nodeNum2Node[nodeNum] = node
                    continue
        lines.close()
        g.nodeNum = max(nodeNum2Node.keys())

        lines = open(filename, 'r')
        for line in lines:
            res = transPattern.match(line)
            if res:
                gid0 = int(res.group(1))
                n0 = int(res.group(2))
                gid1 = int(res.group(3))
                n1 = int(res.group(4))
                if g.gid == None:
                    g.gid = gid0
                elif g.gid != gid0:
                    print('*** Error: graph has multiple ids: %d and %d' % (g.gid, gid0))
                    sys.exit(1)
                if g.gid != gid1:
                    print('*** Error: graph has multiple ids: %d and %d' % (g.gid, gid1))
                    sys.exit(1)
                # print('Transition found : %d -> %d' % (n0, n1))
                node0 = nodeNum2Node[n0]
                node1 = nodeNum2Node[n1]
                node0.children.append(node1)
                node1.parents.append(node0)
        
        l = []
        for n in g.nodes:
            if len(n.parents) == 0:
                l.append(n)
                #print('Adding node %d to nodesToAnalyze: %s' % (n.num, n.expPrint()))
        g.roots = l
        return g
                
        



    def registerNode(self, node):
        self.nodeNum += 1
        node.num = self.nodeNum

        self.nodes.add(node)
        if isinstance(node, SymbNode):
            assert(node.symb not in self.symb2node)
            self.symb2node[node.symb] = node
            if node.symbType == 'M':
                self.maskNodes.add(node)
            elif node.symbType == 'S':
                self.secretNodes.add(node)
            else:
                assert(node.symbType == 'P')

    def deregisterNode(self, node):
        self.nodes.remove(node)
        if isinstance(node, SymbNode):
            del self.symb2node[node.symb]
            if node.symbType == 'M':
                assert(node in self.maskNodes)
                self.maskNodes.remove(node)
            elif node.symbType == 'S':
                assert(node in self.secretNodes)
                self.secretNodes.remove(node)
        elif isinstance(node, ConstNode):
            del self.cst2node[node.width][node.cst]

    def getNode(self, symb):
        return self.symb2node[symb]

    def makeSymbNode(self, symb, symbType, nbBits):
        if symb in self.symb2node:
            if nbBits != self.symb2node[symb].width:
                print('*** Error: symbol %s was already defined on %d bits' % (symb, self.symb2node[symb].width))
                sys.exit(1)
            if symbType != self.symb2node[symb].symbType:
                print('*** Error: symbol %s was already defined as having type %s' % (symb, self.symb2node[symb].symbType))
                sys.exit(1)
            return self.symb2node[symb]
        else:
            n = SymbNode(symb, symbType, self, nbBits)
            return n

    def makeConstNode(self, cst, nbBits):
        if nbBits in self.cst2node.keys():
            if cst in self.cst2node[nbBits].keys():
                return self.cst2node[nbBits][cst]
            else:
                n = ConstNode(cst, self, nbBits)
                self.cst2node[nbBits][cst] = n
                return n
        else:
            self.cst2node[nbBits] = {}
            n = ConstNode(cst, self, nbBits)
            self.cst2node[nbBits][cst] = n
            return n

    def makeOpNode(self, op, children, preserveChildren = None):
        n = OpNode(op, None, children)
        if mergeAssociativeOpsOnBuild:
            n.mergeWithChildrenIfPossible(preserveChildren)
        assert(children != None and children)
        assert(children[0].graph is self)
        return n

    def makeOpNodeNoChildren(self, op):
        n = OpNode(op, self, None)
        return n

    def removeOrphanNodes(self, nodeList):
        gNodesCopy = set(self.nodes) # to avoid concurrent modification of g.nodes with its traversal
        for n in gNodesCopy:
            # retesting if n in self.nodes since a previous call to removeSymbRefs may have already freed it
            if n not in nodeList and n in self.nodes and len(n.parents) == 0:
                n.removeSymbRefs(nodeList)



    def dump(self, filename, dumpParentEdges):
        f = open(filename, 'w')
        content = 'digraph g {\n'
        content += self.asText(dumpParentEdges)
        content += '}'
        f.write(content)
        f.close()


    def asText(self, dumpParentEdges):
        content = ''
        for n in self.nodes:
            if isinstance(n, SymbNode):
                s = 'Symbol: %s [%s]' % (n.symb, n.symbType)
            elif isinstance(n, OpNode):
                if n.op == '|':
                    s = 'Op: \\| (num %d)' % n.num
                elif n.op == '<<':
                    s = 'Op: \\<\\<'
                elif n.op == '>>':
                    s = 'Op: \\>\\>'
                elif n.op == '>>>':
                    s = 'Op: \\>\\>\\>'
                else:
                    s = 'Op: %s (num %d)' % (n.op, n.num)
            elif isinstance(n, ConstNode):
                s = 'Const: %d' % n.cst
            else:
                s = ''
            #content += '   N%d [shape=record, label=\"{{Symbol: %s | Operator: %s}|{Bla}}\"];\n' % (n.num, s, op)
            content += '   G%dN%d [shape=record, label=\"{%s}\"];\n' % (self.gid, n.num, s)
            for a in n.children:
                content += '   edge[tailclip=true];\n'
                content += '   G%dN%d -> G%dN%d\n' % (self.gid, n.num, self.gid, a.num)
            if dumpParentEdges:
                for a in n.parents:
                    content += '   edge[tailclip=true];\n'
                    content += '   G%dN%d -> G%dN%d [style="dashed"]\n' % (self.gid, n.num, self.gid, a.num)
        content += '   G%dRoots [shape=record, label="{{' % self.gid
        for root in range(len(self.roots) - 1):
            content += '<r%d> |' % root
        content += '<r%d> }}"];\n' % (len(self.roots) - 1)
        for root in range(len(self.roots)):
            content += '   edge[tailclip=false];\n'
            content += '   G%dRoots:r%d:c -> G%dN%d [style=dashed]\n' % (self.gid, root, self.gid, self.roots[root].num)
        return content
                    
                
    def simplify(self):
        from simplify import simplify
        for root in self.roots:
            simplify(root, self.roots)


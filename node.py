#!/usr/bin/python

# Copyright (C) 2019, Sorbonne Universite, LIP6
# This file is part of the SELA project, under the GPL v3.0 license
# See https://www.gnu.org/licenses/gpl-3.0.en.html for license information
# SPDX-License-Identifier: GPL-3.0-only
# Author(s): Quentin L. Meunier

from __future__ import print_function


associativeOps = ['^', '+', '&', '|']


class Node(object):

    def __init__(self, children, graph):
        self.children = []
        self.parents = []
        if children != None:
            assert(children)
            assert(graph == None)
            for child in children:
                assert(child.graph is children[0].graph)
                if isinstance(child, FinalNode) or len(child.parents) == 0:
                    assert(isinstance(child, OpNode) or not child.children)
                    self.children.append(child)
                    child.parents.append(self)
                else:
                    assert(isinstance(child, OpNode))
                    duplicatedChild = OpNode(child.op, None, child.children)
                    duplicatedChild.parents = [self]
                    duplicatedChild.width = child.width
                    self.children.append(duplicatedChild)
            self.graph = children[0].graph
        else:
            assert(graph != None)
            self.graph = graph

        self.graph.registerNode(self)

    def deregisterNode(self):
        self.graph.deregisterNode(self)
        self.parents = None
        self.children = None

    def toString(self):
        return '[G%dN%d]' % (self.graph.gid, self.num)

    @staticmethod
    def link(child, parent, childIndex = None):
        child.parents.append(parent)
        if childIndex != None:
            parent.children.insert(childIndex, child)
        else:
            parent.children.append(child)

    @staticmethod
    # FIXME: remove parent and make non-static?
    def unlink(child, parent, childIndex = None):
        child.parents.remove(parent)
        if childIndex != None:
            assert(parent.children[childIndex] is child)
            del parent.children[childIndex]
        else:
            parent.children.remove(child)

    # FIXME: not tested with preserveSelf = True
    def mergeWithParentIfPossible(self, preserveSelf = False):
        if len(self.parents) == 1 and isinstance(self, OpNode) and self.op in associativeOps and self.parents[0].op == self.op:
            if preserveSelf:
                assert(False)
                copiedSelf = self.graph.copyNodeRec(self)
                copiedSelf.parents.append(self.parents[0])
                for i in range(len(self.parents[0].children)):
                    if self.parents.children[i] is self:
                        self.parents.children[i] = copiedSelf
                copiedSelf.merge()
            else:
                self.merge()

    def mergeWithChildrenIfPossible(self, preserveChildren = None):
        if self.op in associativeOps:
            nodesToMerge = []
            for idx in range(len(self.children)):
                child = self.children[idx]
                if isinstance(child, OpNode) and child.op == self.op:
                    if preserveChildren != None and preserveChildren[idx]:
                        copiedChild = self.graph.copyNodeRec(child)
                        copiedChild.parents.append(self)
                        self.children[idx] = copiedChild
                        child.parents.remove(self)
                        nodesToMerge.append(copiedChild)
                    else:
                        nodesToMerge.append(child)
    
            for n in nodesToMerge:
                n.merge()

    def merge(self):
        # Merges self with its parent and deregisters self
        assert(len(self.parents) == 1)
        parent = self.parents[0]
        for grandChild in self.children:
            parent.children.append(grandChild)
            grandChild.parents.remove(self)
            grandChild.parents.append(parent)
        Node.unlink(self, parent)
        self.deregisterNode()
        

    @staticmethod
    def linkChildAndParent(node, nodeList):
        assert(len(node.children) == 1)
        child = node.children[0]

        if len(node.parents) == 0:
            assert(node in nodeList)
            Node.unlink(child, node)
            for idx in range(len(nodeList)):
                if nodeList[idx] is node:
                    nodeList[idx] = child
            node.deregisterNode()
        else:
            assert(len(node.parents) == 1)
            for nodeListIdx in range(len(nodeList)):
                if nodeList[nodeListIdx] is node:
                    nodeList[nodeListIdx] = child

            parent = node.parents[0]
            for i in range(len(parent.children)):
                if parent.children[i] is node:
                    parent.children[i] = child
                    Node.unlink(child, node)
                    child.parents.append(parent)
                    node.deregisterNode()
                    #child.mergeWithParentIfPossible()
                    break

    def removeSymbRefs(self, nodeList):
        # node can have already been removed, e.g. if calling this function on a list of node (for example in Extract)
        # FIXME: still possible?
        # node has been removed <=> self.children == None
        if self in nodeList or self.children == None:
            return
        while len(self.children) > 0:
            child = self.children[0]
            assert(self in child.parents)
            Node.unlink(child, self)
            # removeSymbRefs of child after unlinking it with its parent to allow for
            # the deregistering of a symbNode if it has no parent anymore
            #if child not in nodeList: # Not necessary anymore
            child.removeSymbRefs(nodeList)
    
        if isinstance(self, OpNode):
            self.deregisterNode()
        elif isinstance(self, SymbNode):
            # For symbNodes, deregister if it has no parent anymore and it is not in nodeList
            if len(self.parents) == 0:
                self.deregisterNode()




class FinalNode(Node):
    def __init__(self, graph, width):
        self.width = width
        Node.__init__(self, None, graph)

    #def toString(self):
    #    return Node.toString(self)


class SymbNode(FinalNode):
    def __init__(self, symb, symbType, graph, width):
        self.symb = symb
        self.symbType = symbType
        FinalNode.__init__(self, graph, width)

    def toString(self):
        return super().toString(self) + ' Symb<%d> %s [%s]' % (self.width, self.symb, self.symbType)

    def expPrint(self):
        return '%s' % self.symb

    def __str__(self):
        return self.expPrint()


class ConstNode(FinalNode):
    def __init__(self, cst, graph, width):
        self.cst = cst
        FinalNode.__init__(self, graph, width)

    def toString(self):
        return super().toString(self) + ' Const<%d> %d' % (self.width, self.cst)

    def expPrint(self):
        #return '%d' % self.cst
        return 'Const(%d, %d)' % (self.cst, self.width)

    def __str__(self):
        return self.expPrint()


class OpNode(Node):
    def __init__(self, op, graph, children):
        if graph is None:
            assert(children != None and children)
            self.op = op
            if op == '+' or op == '--' or op == '-' or op == '&' or op == '|' or op == '^' or op == '~' or op == '<<' or op == '>>' or op == '>>>':
                self.width = children[0].width
            elif op == 'ZE' or op == 'SE':
                self.width = children[0].cst + children[1].width
            elif op == 'C':
                width = 0
                for child in children:
                    width += child.width
                self.width = width
            elif op == 'E':
                self.width = children[0].cst - children[1].cst + 1
            elif op == 'A':
                # FIXME?
                self.width = children[0].width
            else:
                print("op = %s" % op)
                assert(False)
            Node.__init__(self, children, None)
        else:
            assert(children is None)
            self.op = op
            Node.__init__(self, None, graph)

    def toString(self):
        return Node.toString(self) + ' Op %s' % self.op

    def expPrint(self):
        if isinstance(self, OpNode) and self.op == '~':
            res = '~' + self.children[0].expPrint()
            return res
        elif isinstance(self, OpNode) and self.op == '-':
            res = '-' + self.children[0].expPrint()
            return res
        elif isinstance(self, OpNode) and self.op == 'ZE':
            res = 'ZeroExt(' + self.children[0].expPrint() + ', ' + self.children[1].expPrint() + ')'
            return res
        elif isinstance(self, OpNode) and self.op == 'SE':
            res = 'SignExt(' + self.children[0].expPrint() + ', ' + self.children[1].expPrint() + ')'
            return res
        elif isinstance(self, OpNode) and self.op == 'C':
            res = 'Concat(' + ', '.join(map(lambda x:x.expPrint(), self.children)) + ')'
            return res
        elif isinstance(self, OpNode) and self.op == 'E':
            res = 'Extract(' + ', '.join(map(lambda x:x.expPrint(), self.children)) + ')'
            return res
        elif isinstance(self, OpNode) and self.op == 'A':
            res = 'A[' + self.children[0].expPrint() + ']'
            return res


        res = '('
        for idx in range(len(self.children)):
            res += self.children[idx].expPrint()
            if idx != len(self.children) - 1:
                res += ' %s ' % self.op
        res += ')'
        return res

    def __str__(self):
        return self.expPrint()




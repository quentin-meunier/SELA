#!/usr/bin/python

# Copyright (C) 2019, Sorbonne Universite, LIP6
# This file is part of the SELA project, under the GPL v3.0 license
# See https://www.gnu.org/licenses/gpl-3.0.en.html for license information
# SPDX-License-Identifier: GPL-3.0-only
# Author(s): Quentin L. Meunier

from __future__ import print_function

from node import *
from graph import *
from simplify import *
from config import *

import sys
import os
import re


class Exp:

    expId = 0

    # nodeList : word node list. If not none,
    # creates an Exp which is a copy of the node list
    def __init__(self, expList = None):
        Exp.expId += 1

        if expList != None:
            wordList = []
            for exp in expList:
                wordList += exp.wordGraph.roots
            self.wordGraph = Graph(self, wordList)

            if bitExpEnable():
                bitList = []
                for exp in expList:
                    bitList += exp.bitGraph.roots
                self.bitGraph = Graph(self, bitList)
            else:
                self.bitGraph = None
        else:
            self.wordGraph = Graph(self)
            if bitExpEnable():
                self.bitGraph = Graph(self)
            else:
                self.bitGraph = None

    def getWidth(self):
        return self.wordGraph.roots[0].width

    def getRoot(self):
        assert(len(self.wordGraph.roots) == 1)
        return self.wordGraph.roots[0]
    
    #def getSymbol(self, symbName):
    #    try:
    #        return Exp(self.symb2node[symbName])
    #    except:
    #        return None

    def expPrint(self):
        return ', '.join(map(lambda x:x.expPrint(), self.wordGraph.roots))

    def __str__(self):
        return self.expPrint()

    def __and__(self, other):
        e = self.makeBitwiseNode('&', [self, other])
        return e

    def __or__(self, other):
        e = self.makeBitwiseNode('|', [self, other])
        return e

    def __xor__(self, other):
        e = self.makeBitwiseNode('^', [self, other])
        return e

    def __invert__(self):
        n = self.makeBitwiseNode('~', [self])
        return n

    def makeBitwiseNode(self, op, children):
        assert(children != None and children)
        width = children[0].getWidth()
        for child in children:
            assert(child.getWidth() == width)
        if propagateCstOnBuild():
            # FIXME: simplify ~(~e) on build?
            allChildrenCst = True
            for child in children:
                if not isinstance(child.getRoot(), ConstNode):
                    allChildrenCst = False
                    break
            if allChildrenCst:
                if op == '&':
                    res = ~0
                else:
                    res = 0
                for child in children:
                    if op == '^':
                        res = res ^ child.getRoot().cst
                    elif op == '&':
                        res = res & child.getRoot().cst
                    elif op == '|':
                        res = res | child.getRoot().cst
                    elif op == '~':
                        res = (1 << width) - 1 - child.getRoot().cst
                return Const(res, width)

        e = Exp(children)

        wordNode = e.wordGraph.makeOpNode(op, e.wordGraph.roots)
        e.wordGraph.roots = [wordNode]

        if bitExpEnable():
            bitRoots = []
            for i in range(width):
                if op == '~':
                    bitNode = e.bitGraph.makeOpNode(op, [e.bitGraph.roots[i]])
                else:
                    bitNode = e.bitGraph.makeOpNode(op, [e.bitGraph.roots[i], e.bitGraph.roots[i + width]])
                bitRoots.append(bitNode)
            e.bitGraph.roots = bitRoots
        return e


    def __add__(self, other):
        child0 = self
        child1 = other
        assert(child0.getWidth() == child1.getWidth())
        width = child0.getWidth()
 
        if propagateCstOnBuild() and isinstance(child0.getRoot(), ConstNode) and isinstance(child1.getRoot(), ConstNode):
            e = Const((child0.getRoot().cst + child1.getRoot().cst) % (1 << width), width)
            return e

        e = Exp([child0, child1])
        wordNode = e.wordGraph.makeOpNode('+', e.wordGraph.roots)
        e.wordGraph.roots = [wordNode]

        
        if bitExpEnable():
            ai = e.bitGraph.roots[0]
            bi = e.bitGraph.roots[width]
            si = e.bitGraph.makeOpNode('^', [ai, bi], preserveChildren = [True, True])
            ci = e.bitGraph.makeOpNode('&', [ai, bi])
            bitRoots = []
            bitRoots.append(si)
            for i in range(1, width):
                ai = e.bitGraph.roots[i]
                bi = e.bitGraph.roots[i + width]
                # preserve nodes in case of merge only if not the last iteration
                si = e.bitGraph.makeOpNode('^', [ai, bi, ci], preserveChildren = [i != width - 1, i != width - 1, i != width - 1])
                bitRoots.append(si)
                if i != width - 1:
                    aiXorbi = e.bitGraph.makeOpNode('^', [ai, bi], preserveChildren = [True, True])
                    aiAndbi = e.bitGraph.makeOpNode('&', [ai, bi])
                    aiXorbiAndci = e.bitGraph.makeOpNode('&', [aiXorbi, ci])
                    ci = e.bitGraph.makeOpNode('|', [aiXorbiAndci, aiAndbi])

            e.bitGraph.roots = bitRoots
        return e


    def __sub__(self, other):
        child0 = self
        child1 = other
        assert(child0.getWidth() == child1.getWidth())
        width = child0.getWidth()

        if propagateCstOnBuild() and isinstance(child0.getRoot(), ConstNode) and isinstance(child1.getRoot(), ConstNode):
            e = Const((child0.getRoot().cst - child1.getRoot().cst) % (1 << width), width)
            return e

        if isinstance(child1.getRoot(), ConstNode):
            return self + Const((-child1.getRoot().cst) % (1 << width), child1.getRoot().width)

        e = Exp([child0, child1])
        negaNode = e.wordGraph.makeOpNode('-', [e.wordGraph.roots[1]])
        wordNode = e.wordGraph.makeOpNode('+', [e.wordGraph.roots[0], negaNode])
        e.wordGraph.roots = [wordNode]

        if bitExpEnable():
            ai = e.bitGraph.roots[0]
            bi = e.bitGraph.roots[width]
            nbi = e.bitGraph.makeOpNode('~', [bi], preserveChildren = [True])
            si = e.bitGraph.makeOpNode('^', [ai, bi], preserveChildren = [True, width > 1])
            ci = e.bitGraph.makeOpNode('|', [ai, nbi], preserveChildren = [False, width > 1])
            bitRoots = []
            bitRoots.append(si)
            for i in range(1, width):
                ai = e.bitGraph.roots[i]
                bi = e.bitGraph.roots[i + width]
                nbi = e.bitGraph.makeOpNode('~', [bi]) # no preserveChildren
                si = e.bitGraph.makeOpNode('^', [ai, nbi, ci], preserveChildren = [i != width - 1, i != width - 1, i != width - 1])
                bitRoots.append(si)
                if i != width - 1:
                    aiXornbi = e.bitGraph.makeOpNode('^', [ai, nbi], preserveChildren = [True, True])
                    aiAndnbi = e.bitGraph.makeOpNode('&', [ai, nbi])
                    aiXornbiAndci = e.bitGraph.makeOpNode('&', [aiXornbi, ci])
                    ci = e.bitGraph.makeOpNode('|', [aiXornbiAndci, aiAndnbi])

            e.bitGraph.roots = bitRoots
        return e


    def __neg__(self):
        child = self
        width = child.getWidth()
        if propagateCstOnBuild() and isinstance(child.getRoot(), ConstNode):
            e = Const((-child.getRoot().cst) % (1 << width), width)
            return e

        e = Exp([child])
        wordNode = e.wordGraph.makeOpNode('-', e.wordGraph.roots)
        e.wordGraph.roots = [wordNode]

        if bitExpEnable():
            ai = e.bitGraph.roots[0]
            nai = e.bitGraph.makeOpNode('~', [ai], preserveChildren = [True])
            si = ai
            ci = nai
            bitRoots = []
            bitRoots.append(si)
            for i in range(1, width):
                ai = e.bitGraph.roots[i]
                nai = e.bitGraph.makeOpNode('~', [ai])
                si = e.bitGraph.makeOpNode('^', [nai, ci], preserveChildren = [i != width - 1, i != width - 1])
                bitRoots.append(si)
                if i != width - 1:
                    ci = e.bitGraph.makeOpNode('&', [nai, ci])

            e.bitGraph.roots = bitRoots
        return e


    def __lshift__(self, shval):
        if isinstance(shval, Exp) and isinstance(shval.getRoot(), ConstNode):
            shval = shval.getRoot().cst
        if not isinstance(shval, int):
            print('*** Error: Second operand of a Shift operation can only be a constant')
            assert(False)

        width = self.getWidth()
        if shval >= width:
            print('*** Warning: shift value (%d) >= bit width of expression (%d)' % (shval, width))

        if propagateCstOnBuild() and isinstance(self.getRoot(), ConstNode):
            e = Const((self.getRoot().cst << shval) % (1 << width), width)
            return e

        e = Exp([self])
        sh = e.wordGraph.makeConstNode(shval, shval.bit_length())

        wordNode = e.wordGraph.makeOpNode('<<', [e.getRoot(), sh])
        e.wordGraph.roots = [wordNode]

        if bitExpEnable():
            bitRoots = []
            for i in range(min(width, shval)):
                cstNode = e.bitGraph.makeConstNode(0, 1)
                bitRoots.append(cstNode)
            for i in range(shval, width):
                bitRoots.append(e.bitGraph.roots[i - shval])

            e.bitGraph.roots = bitRoots
        return e


    def __rshift__(self, shval):
        # Arith Shift Right
        if isinstance(shval, Exp) and isinstance(shval.getRoot(), ConstNode):
            shval = shval.getRoot().cst
        if not isinstance(shval, int):
            print('*** Error: Second operand of a Shift operation can only be a constant')
            assert(False)

        width = self.getWidth()
        if shval >= width:
            print('*** Warning: shift value (%d) >= bit width of expression (%d)' % (shval, width))

        if propagateCstOnBuild() and isinstance(self.getRoot(), ConstNode):
            cst = self.getRoot().cst
            if cst >> (width - 1) == 1: # MSB == 1
                mod = 1 << width
                e = Const(~((~cst % mod) >> shval) % mod, width)
            else:
                e = Const(cst >> shval, width)
            return e

        e = Exp([self])
        sh = e.wordGraph.makeConstNode(shval, shval.bit_length())

        wordNode = e.wordGraph.makeOpNode('>>>', [e.getRoot(), sh])
        e.wordGraph.roots = [wordNode]

        if bitExpEnable():
            bitRoots = []
            for i in range(shval, width):
                bitRoots.append(e.bitGraph.roots[i])
            signBitNode = e.bitGraph.roots[-1]
            for i in range(shval):
                bitRoots.append(e.bitGraph.copyNodeRec(signBitNode))
            for i in range(shval):
                e.bitGraph.roots[i].removeSymbRefs(bitRoots)

            e.bitGraph.roots = bitRoots
        return e


    def dump(self, filename, wordGraph, dumpParentEdges = False):
        if wordGraph or not bitExpEnable():
            self.wordGraph.dump(filename, dumpParentEdges)
        else:
            self.bitGraph.dump(filename, dumpParentEdges)


    def simplifyWords(self):
        self.wordGraph.simplify()

    def simplifyBits(self):
        if bitExpEnable():
            self.bitGraph.simplify()

    def simplify(self):
        self.simplifyWords()
        self.simplifyBits()



# returns a positive litteral integer corresponding to the node value
# if it can be computed, None otherwise
def exp2litteralInteger(e):
    def bitNodes2LitteralInteger(bitNodes):
        res = 0
        v = 1
        for bitNode in bitNodes:
            if isinstance(bitNode, ConstNode):
                res += v * bitNode.cst
                v *= 2
            else:
                return None

    if isinstance(e.getRoot(), ConstNode):
        return e.getRoot().cst

    exp = Exp([e])
    exp.simplifyWords()
    if isinstance(exp.getRoot(), ConstNode):
        return exp.getRoot().cst
    
    if bitExpEnable():
        exp.simplifyBits()
        return bitNodes2LitteralInteger(exp.bitGraph.roots)
    else:
        return None



def LShR(child, shval):
    assert(isinstance(child, Exp))
    assert(len(child.wordGraph.roots) == 1)
    
    e = Exp([child])

    if isinstance(shval, Exp) and isinstance(shval.getRoot(), ConstNode):
        shval = shval.getRoot().cst
    if not isinstance(shval, int):
        print('*** Error: Second operand of a Shift operation can only be a constant')
        assert(False)

    width = child.getWidth()
    if shval >= width:
        print('*** Warning: shift value (%d) >= bit width of expression (%d)' % (shval, width))


    if propagateCstOnBuild() and isinstance(child.getRoot(), ConstNode):
        e = Const(child.getRoot().cst >> shval, width)
        return e

    sh = e.wordGraph.makeConstNode(shval, shval.bit_length())

    wordNode = e.wordGraph.makeOpNode('>>', [e.getRoot(), sh])
    e.wordGraph.roots = [wordNode]

    if bitExpEnable():
        bitRoots = []
        for i in range(shval, width):
            bitRoots.append(e.bitGraph.roots[i])
        for i in range(shval):
            cstNode = e.bitGraph.makeConstNode(0, 1)
            bitRoots.append(cstNode)

        e.bitGraph.roots = bitRoots
    return e



def Concat(*children):
    assert(children != None and children)

    if propagateCstOnBuild():
        allChildrenCst = True
        for child in children:
            if not isinstance(child.getRoot(), ConstNode):
                allChildrenCst = False
                break
        if allChildrenCst:
            cstRes = 0
            currNbBits = 0
            for child in children:
                cstRes = cstRes << child.getRoot().width
                cstRes += child.getRoot().cst
                currNbBits += child.getRoot().width
            newConstExp = Const(cstRes, currNbBits)
            return newConstExp

    e = Exp(children[::-1])
    wordNode = e.wordGraph.makeOpNode('C', e.wordGraph.roots)
    e.wordGraph.roots = [wordNode]
    # Nothing to do for bitGraph (roots already set)
    return e


def Extract(msb, lsb, child):
    assert(isinstance(child, Exp))
    
    if isinstance(msb, Exp) and isinstance(msb.getRoot(), ConstNode):
        msb = msb.getRoot().cst
    if isinstance(lsb, Exp) and isinstance(lsb.getRoot(), ConstNode):
        lsb = lsb.getRoot().cst

    if not isinstance(msb, int) or not isinstance(lsb, int):
        print('*** Error: msb and lsb parameters of makeExtractNode must be integer constants')
        assert(False)

    if msb < lsb:
        print('*** Error: msb must be greater or equal than lsb')
        assert(False)

    width = child.getWidth()
    if msb < 0 or msb > width or lsb < 0 or lsb > width:
        print('*** Error: msb and lsb parameters must be comprised between 0 and %d' % width)
        assert(False)

    if propagateCstOnBuild() and isinstance(child.getRoot(), ConstNode):
        # Directly create a const node
        cst = child.getRoot().cst
        assert(cst >= 0)
        cstString = format(cst, '0%db' % width)[::-1]
        newCstString = cstString[lsb:msb + 1]
        newCst = int(newCstString[::-1], 2)
        e = Const(newCst, msb - lsb + 1)
        return e

    # Since there is no more reference duplication in roots,
    # the process for removing useless nodes in simpler
    e = Exp([child])
    msbNode = e.wordGraph.makeConstNode(msb, msb.bit_length())
    lsbNode = e.wordGraph.makeConstNode(lsb, lsb.bit_length())
    wordNode = e.wordGraph.makeOpNode('E', [msbNode, lsbNode, e.getRoot()])
    e.wordGraph.roots = [wordNode]

    if bitExpEnable():
        newBitRoots = e.bitGraph.roots[lsb:msb + 1]
        #bitRootsToRemove = [elem for elem in e.bitGraph.roots if elem not in newBitRoots]
        bitRootsToRemove = e.bitGraph.roots[0:lsb] + e.bitGraph.roots[msb + 1:width]
        for bitRootToRemove in bitRootsToRemove:
            bitRootToRemove.removeSymbRefs(newBitRoots)
        e.bitGraph.roots = newBitRoots

    if simplifyOnBuild:
        simplifyExtract(e.getRoot(), e.wordGraph.roots)
    return e


def ZeroExt(numZeros, child):
    assert(isinstance(child, Exp))
    childRoot = child.getRoot()

    if isinstance(numZeros, Exp) and isinstance(numZeros.getRoot(), ConstNode):
        numZeros = numZero.getRoot().cst

    if not isinstance(numZeros, int):
        print('*** Error: numZeros must be an integer constant')
        assert(False)

    if numZeros <= 0:
        print('*** Error: numZeros must be greater than 0')
        assert(False)

    if propagateCstOnBuild() and isinstance(childRoot, ConstNode):
        cst = childRoot.cst
        assert(cst >= 0)
        e = Const(cst, childRoot.width + numZeros)
        return e

    e = Exp([child])
    numZerosNode = e.wordGraph.makeConstNode(numZeros, numZeros.bit_length())
    wordNode = e.wordGraph.makeOpNode('ZE', [numZerosNode, e.getRoot()])
    e.wordGraph.roots = [wordNode]

    if bitExpEnable():
        zeroConst = e.bitGraph.makeConstNode(0, 1)
        for i in range(numZeros):
            e.bitGraph.roots.append(zeroConst)
    return e


def SignExt(numSignBits, child):
    assert(isinstance(child, Exp))
    childRoot = child.getRoot()

    if isinstance(numSignBits, Exp) and isinstance(numSignBits.getRoot(), ConstNode):
        numSignBits = numSignBits.getRoot().cst

    if not isinstance(numSignBits, int):
        print('*** Error: numSignBits must be an integer constant')
        assert(False)

    if numSignBits <= 0:
        print('*** Error: numSignBits must be greater than 0')
        assert(False)

    if propagateCstOnBuild() and isinstance(childRoot, ConstNode):
        width = childRoot.width
        cst = childRoot.cst
        assert(cst >= 0)
        if cst >> (width - 1) == 1: # MSB == 1
            cst = (1 << (width + numSignBits)) + (cst - (1 << width))
        e = Const(cst, width + numSignBits)
        return e

    e = Exp([child])
    numSignBitsNode = e.wordGraph.makeConstNode(numSignBits, numSignBits.bit_length())
    wordNode = e.wordGraph.makeOpNode('SE', [numSignBitsNode, e.getRoot()])
    e.wordGraph.roots = [wordNode]

    if bitExpEnable():
        signBitNode = e.bitGraph.roots[-1]
        for i in range(numSignBits):
            e.bitGraph.roots.append(e.bitGraph.copyNodeRec(signBitNode))
    return e




class Symb(Exp):
    def __init__(self, symb, symbType, width):
        self.wordGraph = Graph(self)
        self.bitGraph = Graph(self)

        n = self.wordGraph.makeSymbNode(symb, symbType, width)
        self.wordGraph.roots = [n]

        if bitExpEnable():
            l = []
            for i in range(width):
                bitNode = self.bitGraph.makeSymbNode('%s#%d' % (symb, i), symbType, 1)
                l.append(bitNode)
            self.bitGraph.roots = l


class Const(Exp):
    def __init__(self, cst, width):
        self.wordGraph = Graph(self)
        self.bitGraph = Graph(self)
        if cst >= 0:
            if cst.bit_length() > width:
                print('*** Error: constant %d cannot be coded on %d bits' % (cst, width))
                assert(False)
            wordNode = self.wordGraph.makeConstNode(cst, width)
            self.wordGraph.roots = [wordNode]

            if bitExpEnable():
                l = []
                cstText = bin(cst)[2:]
                for i in reversed(range(len(cstText))):
                    bitNode = self.bitGraph.makeConstNode(int(cstText[i]), 1)
                    l.append(bitNode)
                for i in range(len(cstText), width):
                    bitNode = self.bitGraph.makeConstNode(0, 1)
                    l.append(bitNode)
                self.bitGraph.roots = l
        else:
            if cst < -(1 << (width - 1)):
                print('*** Error: constant %d cannot be coded on %d bits' % (cst, width))
                assert(False)
            # Storing positive value
            cst = cst % (1 << width)
            wordNode = self.wordGraph.makeConstNode(cst, width)
            self.wordGraph.roots = [wordNode]

            if bitExpEnable():
                l = []
                cstText = bin(cst)[2:]
                #cstText = '{:b}'.format(cst & (1 << width) - 1)
                for i in reversed(range(len(cstText))):
                    bitNode = self.bitGraph.makeConstNode(int(cstText[i]), 1)
                    l.append(bitNode)
                for i in range(len(cstText), width):
                    bitNode = self.bitGraph.makeConstNode(0, 1)
                    l.append(bitNode)
                self.bitGraph.roots = l


    def getConst(self):
        return self.getRoot().cst



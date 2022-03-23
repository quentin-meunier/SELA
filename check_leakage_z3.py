#!/usr/bin/python

# Copyright (C) 2019, Sorbonne Universite, LIP6
# This file is part of the SELA project, under the GPL v3.0 license
# See https://www.gnu.org/licenses/gpl-3.0.en.html for license information
# SPDX-License-Identifier: GPL-3.0-only
# Author(s): Quentin L. Meunier

from __future__ import print_function
import timeit

from z3 import *

from graph import *
from ni import *
from utils import *


bitExprs = dict()

class AstRefKey(object):
    def __init__(self, n):
        self.n = n
    def __hash__(self):
        return self.n.hash()
    def __eq__(self, other):
        return self.n.eq(other.n)
    def __repr__(self):
        return str(self.n)

def asKey(n):
    assert isinstance(n, AstRef)
    return AstRefKey(n)



def __simpZ3ExpBit(e):
    # Create a z3 exp equivalent to the z3 expression e, but with the following substitutions:
    # ...
    # And returns a list of z3 bit expressions
    # Warning: the result of calls to __simpZ3ExpBit must be copied into a new list if it is intended to me modified,
    #          otherwise it would invalidate the reference in the map
    ake = asKey(e)
    if ake in bitExprs:
        return bitExprs[ake]

    op = e.decl().kind()
    if op == Z3_OP_BXOR:
        res = list(__simpZ3ExpBit(z3.simplify(e.arg(0))))
        for i in range(1, e.num_args()):
            r = __simpZ3ExpBit(z3.simplify(e.arg(i)))
            for b in range(len(r)):
                res[b] = z3.simplify(res[b] ^ r[b])
        bitExprs[ake] = res
        return res
    elif op == Z3_OP_BAND:
        res = list(__simpZ3ExpBit(z3.simplify(e.arg(0))))
        for i in range(1, e.num_args()):
            r = __simpZ3ExpBit(z3.simplify(e.arg(i)))
            for b in range(len(r)):
                res[b] = z3.simplify(res[b] & r[b])
        bitExprs[ake] = res
        return res
    elif op == Z3_OP_BOR:
        res = list(__simpZ3ExpBit(z3.simplify(e.arg(0))))
        for i in range(1, e.num_args()):
            r = __simpZ3ExpBit(z3.simplify(e.arg(i)))
            for b in range(len(r)):
                res[b] = z3.simplify(res[b] | r[b])
        bitExprs[ake] = res
        return res
    elif op == Z3_OP_BADD:
        if e.num_args() != 2:
            print('num args : %d' % e.num_args())
        assert(e.num_args() == 2)
        e0 = __simpZ3ExpBit(e.arg(0))
        e1 = __simpZ3ExpBit(e.arg(1))
        a0 = e0[0]
        b0 = e1[0]
        res = [z3.simplify(a0 ^ b0)]
        ci = a0 & b0
        for i in range(1, len(e0)):
            ai = e0[i]
            bi = e1[i]
            si = z3.simplify(ai ^ bi ^ ci)
            res.append(si)
            if i != len(e0) - 1:
                ci = z3.simplify(((ai ^ bi) & ci) | (ai & bi))
        bitExprs[ake] = res
        return res
    elif op == Z3_OP_BSUB:
        e0 = __simpZ3ExpBit(e.arg(0))
        e1 = __simpZ3ExpBit(e.arg(1))
        ai = e0[0]
        bi = e1[0]
        nbi = ~bi
        res = [z3.simplify(ai ^ bi)]
        ci = ai | nbi
        for i in range(1, len(e0)):
            ai = e0[i]
            bi = e1[i]
            nbi = ~bi
            si = z3.simplify(ai ^ nbi ^ ci)
            res.append(si)
            if i != len(e0) - 1:
                ci = z3.simplify(((ai ^ nbi) & ci) | (ai & nbi))
        bitExprs[ake] = res
        return res
    elif op == Z3_OP_BNOT:
        # Patching z3 here so that it can merge the xors and simplify in exps like '~k ^ ~(k ^ m)'
        e0 = e.arg(0)
        #if e0.decl().kind() == Z3_OP_BXOR:
        #    res = list(__simpZ3ExpBit(e0.arg(0)))
        #    for b in range(len(res)):
        #        res[b] = z3.simplify(~res[b])
        #    for i in range(1, e0.num_args()):
        #        ei = __simpZ3ExpBit(e0.arg(i))
        #        for b in range(len(ei)):
        #            res[b] = z3.simplify(res[b] ^ ei[b])
        #    bitExprs[ake] = res
        #    return res
        #else:
        #    res = list(__simpZ3ExpBit(e0))
        #    for b in range(len(res)):
        #        res[b] = z3.simplify(~res[b])
        #    bitExprs[ake] = res
        #    return res
        #####
        r = __simpZ3ExpBit(e0)
        res = [0] * len(r)
        for b in range(len(r)):
            if r[b].decl().kind() == Z3_OP_BXOR:
                c0 = ~r[b].arg(0)
                for i in range(1, r[b].num_args()):
                    c0 = z3.simplify(c0 ^ r[b].arg(i))
                res[b] = c0
            else:
                res[b] = z3.simplify(~r[b])
        bitExprs[ake] = res
        return res
        #####
    elif op == Z3_OP_CONCAT:
        res = []
        for i in range(e.num_args() - 1, -1, -1):
            # LSB is the last element in concat, but at first index in list
            res += __simpZ3ExpBit(e.arg(i))
        bitExprs[ake] = res
        return res
    elif op == Z3_OP_EXTRACT:
        res = list(__simpZ3ExpBit(e.arg(0)))
        idx0 = e.params()[0]
        idx1 = e.params()[1]
        res = res[idx1:idx0 + 1]
        bitExprs[ake] = res
        return res
    elif op == Z3_OP_BASHR:
        e0 = __simpZ3ExpBit(e.arg(0))
        shval = e.arg(1)
        signBit = e0[-1]
        res = []
        for i in range(shval.as_long()):
            res.append(signBit)
        for i in range(len(e0) - 1, shval.as_long() - 1, -1):
            res.insert(0, e0[i])
        bitExprs[ake] = res
        return res
    elif op == Z3_OP_BLSHR:
        e0 = __simpZ3ExpBit(e.arg(0))
        shval = e.arg(1)
        res = []
        for i in range(shval.as_long()):
            res.append(BitVecVal(0, 1))
        for i in range(len(e0) - 1, shval.as_long() - 1, -1):
            res.insert(0, e0[i])
        bitExprs[ake] = res
        return res
    elif op == Z3_OP_BSHL:
        e0 = __simpZ3ExpBit(e.arg(0))
        shval = e.arg(1)
        res = []
        for i in range(shval.as_long()):
            res.append(BitVecVal(0, 1))
        for i in range(len(e0) - shval.as_long()):
            res.append(e0[i])
        bitExprs[ake] = res
        return res
    elif op == Z3_OP_ZERO_EXT:
        e0 = __simpZ3ExpBit(e.arg(0))
        extVal = e.params()[0]
        res = []
        for i in range(len(e0)):
            res.append(e0[i])
        for i in range(extVal):
            res.append(BitVecVal(0, 1))
        bitExprs[ake] = res
        return res
    elif op == Z3_OP_SIGN_EXT:
        e0 = __simpZ3ExpBit(e.arg(0))
        extVal = e.params()[0]
        signBit = e0[-1]
        res = []
        for i in range(len(e0)):
            res.append(e0[i])
        for i in range(extVal):
            res.append(signBit)
        bitExprs[ake] = res
        return res
    elif op == Z3_OP_SELECT:
        r = list(__simpZ3ExpBit(e.arg(1)))
        r = z3.simplify(Concat(*r[::-1]))
        res = []
        for b in range(e.size()):
            res.append(Extract(b, b, Select(e.arg(0), r)))
        bitExprs[ake] = res
        return res
    elif op == Z3_OP_BMUL:
        cst = e.arg(0).as_long()
        if cst == (1 << e.size()) - 1:
            v = __simpZ3ExpBit(e.arg(1))
            ai = v[0]
            res = [ai]
            ci = z3.simplify(~ai)
            for i in range(1, len(v)):
                ai = v[i]
                si = z3.simplify(~ai ^ ci)
                res.append(si)
                if i != len(v) - 1:
                    ci = z3.simplify(~ai & ci)
            bitExprs[ake] = res
            return res
        else:
            assert(False)
    elif is_const(e):
        if op == Z3_OP_UNINTERPRETED:
            # variable
            name = e.decl().name()
            res = list(getBitBitVec(name))
            return res
        # constant
        try:
            a = e.as_long()
        except:
            print('*** Error: e not constant')
            assert(False)
        res = []
        #print('cst : %s - size : %d' % (e, e.size()))
        for i in range(e.size()):
            res.append(z3.simplify(Extract(i, i, e)))
        return res
    else:
        # default case
        print(e)
        assert(False)
        res = []
        for b in range(e.size()):
            r = z3.simplify(Extract(b, b, e))
            res.append(r)
        bitExprs[ake] = res
        return res



def __z3BitExp(z3Exp):
    #print('### Init exp to bit-slice: %s' % e)
    e = __simpZ3ExpBit(z3Exp)
    return e


def __createNode(g, exp, bitExp):
    def makeChildren():
        l = []
        for child in exp.children():
            n = __createNode(g, child, bitExp)
            l.append(n)
        return l

    if is_const(exp):
        # Leaf
        #print('Const exp : %s' % exp)

        if exp.decl().kind() == Z3_OP_UNINTERPRETED:
            name = exp.decl().name()
            if bitExp:
                if name in getMaskSymbBitList():
                    nature = 'M'
                elif name in getSecretSymbBitList():
                    nature = 'S'
                else:
                    assert(name in getPublicSymbBitList())
                    nature = 'P'
                return g.makeSymbNode('%s' % name, nature, 1)
            else:
                width = getBitVec(name).size()
                if name in getMaskSymbList():
                    nature = 'M'
                elif name in getSecretSymbList():
                    nature = 'S'
                else:
                    assert(name in getPublicSymbList())
                    nature = 'P'
                return g.makeSymbNode('%s' % name, nature, width)

        if exp.decl().kind() == Z3_OP_EXTRACT:
            assert(False)
        # get python integer
        try:
            v = exp.as_long()
        except:
            assert(False)
        return g.makeConstNode(v, exp.size())

    # Not a leaf
    #print('Non const exp : %s' % exp)
    if bitExp and exp.decl().kind() == Z3_OP_EXTRACT:
        ##print('num_args : %d' % exp.num_args())
        idx0 = exp.params()[0]
        idx1 = exp.params()[1]

        if exp.arg(0).decl().kind() == Z3_OP_SELECT:
            # Returning extract
            child = __createNode(g, exp.arg(0), bitExp)
            idxNode0 = g.makeConstNode(idx0, idx0.bit_length())
            idxNode1 = g.makeConstNode(idx1, idx1.bit_length())
            return g.makeOpNode('E', [idxNode0, idxNode1, child])

        print('Non treated exp : %s' % exp)
        assert(False)

   
    if exp.decl().kind() == Z3_OP_BXOR:
        return g.makeOpNode('^', makeChildren())
    if exp.decl().kind() == Z3_OP_BNOT:
        l = makeChildren()
        assert(len(l) == 1)
        return g.makeOpNode('~', l)
    if exp.decl().kind() == Z3_OP_BOR:
        return g.makeOpNode('|', makeChildren())
    if exp.decl().kind() == Z3_OP_BAND:
        return g.makeOpNode('&', makeChildren())
    if exp.decl().kind() == Z3_OP_BADD:
        if bitExp:
            assert(False)
        else:
            return g.makeOpNode('+', makeChildren())
    if exp.decl().kind() == Z3_OP_BSUB:
        assert(not bitExp)
        assert(len(exp.children()) == 2)
        c0 = __createNode(g, exp.children()[0], bitExp)
        c1 = __createNode(g, exp.children()[1], bitExp)
        if isinstance(c1, ConstNode):
            nc1 = g.makeConstNode((-c1.cst) % (1 << c1.width), c1.width)
        else:
            nc1 = g.makeOpNode('-', [c1])
        l = [c0, nc1]
        return g.makeOpNode('+', l)
    if exp.decl().kind() == Z3_OP_BASHR:
        assert(not bitExp)
        return g.makeOpNode('>>>', makeChildren())
    if exp.decl().kind() == Z3_OP_BLSHR:
        assert(not bitExp)
        return g.makeOpNode('>>', makeChildren())
    if exp.decl().kind() == Z3_OP_BSHL:
        assert(not bitExp)
        return g.makeOpNode('<<', makeChildren())
    if exp.decl().kind() == Z3_OP_EXTRACT:
        assert(not bitExp)
        l = makeChildren()
        assert(len(l) == 1)
        msb = exp.params()[0]
        msb = g.makeConstNode(msb, msb.bit_length())
        lsb = exp.params()[1]
        lsb = g.makeConstNode(lsb, lsb.bit_length())
        l.insert(0, msb)
        l.insert(0, lsb)
        return g.makeOpNode('E', l)
    if exp.decl().kind() == Z3_OP_CONCAT:
        # bitExp can be True since we make Concat of expressions used as indexes (SELECT)
        return g.makeOpNode('C', makeChildren())
    if exp.decl().kind() == Z3_OP_ZERO_EXT:
        assert(not bitExp)
        l = makeChildren()
        extVal = exp.params()[0]
        extVal = g.makeConstNode(extVal, extVal.bit_length())
        l.insert(0, extVal)
        return g.makeOpNode('ZE', l)
    if exp.decl().kind() == Z3_OP_SIGN_EXT:
        assert(not bitExp)
        l = makeChildren()
        extVal = exp.params()[0]
        extVal = g.makeConstNode(extVal, extVal.bit_length())
        l.insert(0, extVal)
        return g.makeOpNode('SE', l)
    if exp.decl().kind() == Z3_OP_BMUL:
        cst = exp.arg(0).as_long()
        if cst == (1 << exp.size()) - 1:
            if bitExp:
                assert(False)
            else:
                l = []
                l.append(__createNode(g, exp.arg(1), bitExp))
                return g.makeOpNode('-', l)
        else:
            assert(False)
 
    if exp.decl().kind() == Z3_OP_SELECT:
        # arrName = exp.arg(0).decl().name()
        child = z3.simplify(exp.arg(1))
        n = __createNode(g, child, bitExp)
        l = [n]
        return g.makeOpNode('A', l)

    print('Non supported exp: %s' % exp)
    assert(False)
    return None



def __createGraph(z3Exp, bitExp):
    g = Graph(None)
    
    l = []
    if bitExp:
        e = __z3BitExp(z3Exp)
        #print('# Exp after z3 -> z3 simplification :')
        #for b in range(len(e)):
        #    print('## b%d: %s' % (b, e[b]))
        for b in range(len(e)):
            #print('# exp for bit %d :\n%s' % (b, e[b]))
            n = __createNode(g, e[b], True)
            #print('# node for bit %d :\n%s' % (b, n))
            l.append(n)
    else:
        n = __createNode(g, z3Exp, False)
        l.append(n)

    g.roots = l
    return g


def __createGraphTrans(z3Exp0, z3Exp1, bitExp):
    g = Graph(None)
    
    l = []
    if bitExp:
        #print('size : %d' % z3Exp.sort().size())
        e = __z3BitExp(z3Exp0)
        for b in range(len(e)):
            n = __createNode(g, e[b], True)
            l.append(n)

        e = __z3BitExp(z3Exp1)
        for b in range(len(e)):
            n = __createNode(g, e[b], True)
            l.append(n)
    else:
        e0 = z3.simplify(z3Exp0)
        n0 = __createNode(g, e0, False)
        e1 = z3.simplify(z3Exp1)
        n1 = __createNode(g, e1, False)
        l.append(n0)
        l.append(n1)

    g.roots = l
    return g


def __createGraphTransBit(z3Exp0, z3Exp1, b):
    g = Graph(None)
    
    l = []
    e = __z3BitExp(z3Exp0)
    n = __createNode(g, e[b], True)
    l.append(n)

    e = __z3BitExp(z3Exp1)
    n = __createNode(g, e[b], True)
    l.append(n)

    g.roots = l
    return g


def __createGraphTransXor(z3Exp0, z3Exp1, bitExp):
    g = Graph(None)
    
    l = []
    if bitExp:
        #print('size : %d' % z3Exp.sort().size())
        e0 = __z3BitExp(z3Exp0)
        e1 = __z3BitExp(z3Exp1)
        for b in range(len(e0)):
            n0 = __createNode(g, e0[b], True)
            n1 = __createNode(g, e1[b], True)
            n = g.makeOpNode('^', [n0, n1])
            l.append(n)
    else:
        e0 = z3.simplify(z3Exp0)
        n0 = __createNode(g, e0, False)
        e1 = z3.simplify(z3Exp1)
        n1 = __createNode(g, e1, False)
        n = g.makeOpNode('^', [n0, n1])
        l.append(n)

    g.roots = l
    return g


def __createGraphTransXorBit(z3Exp0, z3Exp1, b):
    g = Graph(None)
    
    l = []
    e0 = __z3BitExp(z3Exp0)
    n0 = __createNode(g, e0[b], True)
    e1 = __z3BitExp(z3Exp1)
    n1 = __createNode(g, e1[b], True)
    n = g.makeOpNode('^', [n0, n1])
    l.append(n)

    g.roots = l
    return g


def checkNIVal_(z3Exp):
    niTimerStart = timeit.default_timer()
    g = __createGraph(z3Exp, False)

    resNi = ni(g, False)
    if not resNi and bitExpEnable():
        g = __createGraph(z3Exp, True)
        usedBitExp = True
        resNi = ni(g, False)
    else:
        usedBitExp = False

    niTimerEnd = timeit.default_timer()
    niTime = niTimerEnd - niTimerStart
    return resNi, usedBitExp, niTime


def checkNITrans_(z3Exp0, z3Exp1):
    niTimerStart = timeit.default_timer()
    g = __createGraphTrans(z3Exp0, z3Exp1, False)

    resNi = ni(g, False)
    if not resNi and bitExpEnable():
        g = __createGraphTrans(z3Exp0, z3Exp1, True)
        usedBitExp = True
        resNi = ni(g, False)
    else:
        usedBitExp = False

    niTimerEnd = timeit.default_timer()
    niTime = niTimerEnd - niTimerStart
    return resNi, usedBitExp, niTime


def checkNITransBit_(z3Exp0, z3Exp1):
    if bitExpEnable():
        niTime = 0

        assert(z3Exp0.sort().size() == z3Exp1.sort().size())

        for b in range(z3Exp0.sort().size()):
            niTimerStart = timeit.default_timer()
            g = __createGraphTransBit(z3Exp0, z3Exp1, b)

            resNi = ni(g, False)
            niTimerEnd = timeit.default_timer()
            niTime += niTimerEnd - niTimerStart

            if not resNi:
                break

        return resNi, niTime
    else:
        return False, 0


def checkNITransXor_(z3Exp0, z3Exp1):
    niTimerStart = timeit.default_timer()
    g = __createGraphTransXor(z3Exp0, z3Exp1, False)

    resNi = ni(g, False)
    if not resNi and bitExpEnable():
        g = __createGraphTransXor(z3Exp0, z3Exp1, True)
        usedBitExp = True
        resNi = ni(g, False)
    else:
        usedBitExp = False

    niTimerEnd = timeit.default_timer()
    niTime = niTimerEnd - niTimerStart
    return resNi, usedBitExp, niTime


def checkNITransXorBit_(z3Exp0, z3Exp1):
    if bitExpEnable():
        niTime = 0

        assert(z3Exp0.sort().size() == z3Exp1.sort().size())

        for b in range(z3Exp0.sort().size()):
            niTimerStart = timeit.default_timer()
            g = __createGraphTransXorBit(z3Exp0, z3Exp1, b)

            resNi = ni(g, False)
            niTimerEnd = timeit.default_timer()
            niTime += niTimerEnd - niTimerStart

            if not resNi:
                break

        return resNi, niTime
    else:
        return False, 0



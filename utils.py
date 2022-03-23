#!/usr/bin/python
# -*- coding: utf-8 -*-

# Copyright (C) 2019, Sorbonne Universite, LIP6
# This file is part of the SELA project, under the GPL v3.0 license
# See https://www.gnu.org/licenses/gpl-3.0.en.html for license information
# SPDX-License-Identifier: GPL-3.0-only
# Author(s): Quentin L. Meunier

from __future__ import print_function

from simplify import *
from ni import ni, niOrig
from config import *
if useBuiltinExp():
    from exp import *
else:
    import z3
    secretSymbList = []
    secretSymbBitList = []
    maskSymbList = []
    maskSymbBitList = []
    publicSymbList = []
    publicSymbBitList = []
    symbName2BitVec = {}
    symbName2BitBitVec = {}
registeredArrays = {}


class MemArray:
    def __init__(self, name, addr, size, func):
        self.name = name
        self.addr = addr
        self.size = size
        self.func = func


def registerArray(name, addr, size, func):
    if addr != None:
        key = addr
    else:
        key = name

    if key in registeredArrays:
        print('*** Error: Array with key %s already registered' % str(key))
        assert(False)

    arr = MemArray(name, addr, size, func)
    registeredArrays[key] = arr


def getRegisteredArray(key):
    return registeredArrays[key]


def usage(name):
    print("usage: %s [-f <filename> -a ['distrib' | 'NI'] -m ['value' | transition'] -t [0-5]" % name)
    print("Check distribution of one or several formula(s) using a symbolic enumeration.")
    print("Options:")
    print("   -h            : display this help")
    print("   -f <filename> : filename is the output of the analysis ")
    print("   -a ['distrib' | 'NI'] : analysis type" )
    print("   -m ['value' | transition'] : leakage model")
    print("   -t [0-5] : trace level: 0 = no trace, 5 = debug trace")


def checkResults(res, ref):
    assert(isinstance(res, Exp))
    assert(isinstance(ref, Exp))

    nbBits = ref.getWidth()
    
    if nbBits != res.getWidth():
        print('KO (nbBits on res: %d -- expected %d)' % (res.getWidth(), nbBits))

    res.simplify()
    ref.simplify()

    print('ref : %s' % ref.getRoot().expPrint())
    print('res : %s' % res.getRoot().expPrint())

    if nbBits != res.getWidth() or nbBits != ref.getWidth():
        print('KO (nbBits after simplify: res: %d - ref: %d - expected: %d)' % (res.getWidth(), ref.getWidth(), nbBits))
    
    if equivalence(res.getRoot(), ref.getRoot()):
        print('OK')
    else:
        print('KO')
    
    if bitExpEnable():
        ok = True
        for b in range(nbBits):
            if not equivalence(res.bitGraph.roots[b], ref.bitGraph.roots[b]):
                ok = False
                break
        if ok:
            print('OK')
        else:
            print('KO')



def checkNIStrategies(graph, refResult, NIOrig = False):
    refResultTxt = refResult and 'NI' or 'Not NI'
    length = max(map(lambda x:len(x), strategies))
    def strSpace(s, length):
        l = len(s)
        return s + ' ' * (length - l)
    print('Expected Result: %s' % refResultTxt)
    print('[%s]' % (NIOrig and 'NiOrig' or 'NI'))
    for strategy in strategies:
        setSimplifyStrategy(strategy)
        if NIOrig:
            res = niOrig(graph)
        else:
            res = ni(graph)
        print('[%s]: ' % strSpace(strategy, length), end = '')
        if refResult:
            if res:
                print('OK (NI)')
            else:
                print('KO (NI missed)')
        else:
            if res:
                print('ERROR (NI found)')
            else:
                print('OK (not NI)')
    


def printLevel(level, output, s):
    #global trace_level # ?
    if level <= trace_level:
        output.write(s)


def parseArgs(argv):
    i = 1
    if len(argv) < 5:
        usage(argv[0])
        sys.exit(1)
    while i != len(argv):
        #print_level(5, stdout, "analyzing arg %s" % argv[i])
        if argv[i] == "-h":
            usage(argv[0])
            sys.exit(0)
        elif argv[i] == "-f":
            i += 1
            global output
            output = open(argv[i], 'w')
        elif argv[i] == "-m":
            i += 1
            global model
            model = argv[i]
            if model != "value" and model != "transition-reg" and model != "transition-mem":
                print("*** Error: unknown leakage model: %s", argv[i])
                usage(argv[0])
                sys.exit(1)
        elif argv[i] == "-t":
            i += 1
            global trace_level
            trace_level = int(argv[i])
            if argv[i] >= 0 and argv[i] <= 5:
                print("*** Error: trace_level must be between 0 and 5")
                usage(argv[0])
                sys.exit()
        elif argv[i] == "-a":
            i += 1
            global analysis
            analysis = argv[i]
            if argv[i] != "distrib" and argv[i] != "NI":
                print("*** Error : unknown analysis type: %s", argv[i])
                usage(argv[0])
                sys.exit(1)      
        else:
            print("*** Error: unknown option: %s", argv[i])
            usage(argv[0])
            sys.exit(1)
        i += 1
    return output, analysis, model, trace_level


def displayResults(nbNIInsts, nonNIInsts, totalTime):
    print('Nb. instructions analyzed: %d' % (nbNIInsts + len(nonNIInsts)))
    print('Nb NI instructions: %d' % nbNIInsts)
    print('Nb non-NI instructions: %d' % len(nonNIInsts))
    if len(nonNIInsts) != 0:
        print('Non NI instructions:')
        nonNIInsts.sort()
        m = {}
        for addr in nonNIInsts:
            if addr in m:
                m[addr] += 1
            else:
                m[addr] = 1
        l = m.keys()
        l.sort()
        for addr in l:
            print('[%s] : %d' % (addr, m[addr]))
    print('Total Time: %f' % totalTime)


def constant(val, width):
    if useBuiltinExp():
        return Const(val, width)
    else:
        return z3.BitVecVal(val, width)


def symbol(name, nature, width):
    if useBuiltinExp():
        return Symb(name, nature, width)
    else:
        global symbName2BitVec
        global symbName2BitBitVec
        s = z3.BitVec(name, width)
        sb = []
        for i in range(width):
            b = z3.BitVec(name + '#' + str(i), 1)
            sb.append(b)
        symbName2BitVec[name] = s
        symbName2BitBitVec[name] = sb
        if nature == 'S':
            global secretSymbList
            global secretSymbBitList
            secretSymbList.append(name)
            for i in range(width):
                secretSymbBitList.append(name + '#' + str(i))
        elif nature == 'M':
            global maskSymbList
            global maskSymbBitList
            maskSymbList.append(name)
            for i in range(width):
                maskSymbBitList.append(name + '#' + str(i))
        elif nature == 'P':
            global publicSymbList
            global publicSymbBitList
            publicSymbList.append(name)
            for i in range(width):
                publicSymbBitList.append(name + '#' + str(i))
        return s


def simp(e):
    # has a side effect on builtin exps
    if useBuiltinExp():
        e.simplify()
        return e
    else:
        return z3.simplify(e, bv_extract_prop = True)


def litteralInteger(e):
    if isinstance(e, int):
        return e
    if useBuiltinExp():
        return exp2litteralInteger(e)
    else:
        try:
            res = e.as_long()
        except:
            a = z3.simplify(e)
            try:
                res = a.as_long()
            except:
                return None
        return res
        

def width(e):
    if useBuiltinExp():
        return e.getWidth()
    else:
        return e.sort().size()


def getSecretSymbList():
    if useBuiltinExp():
        import sys
        print('### Warning: function %s should not be used with builtin expressions' % sys._getframe.f_code.co_name)
    return secretSymbList


def getSecretSymbBitList():
    if useBuiltinExp():
        import sys
        print('### Warning: function %s should not be used with builtin expressions' % sys._getframe.f_code.co_name)
    return secretSymbBitList


def getMaskSymbList():
    if useBuiltinExp():
        import sys
        print('### Warning: function %s should not be used with builtin expressions' % sys._getframe.f_code.co_name)
    return maskSymbList


def getMaskSymbBitList():
    if useBuiltinExp():
        import sys
        print('### Warning: function %s should not be used with builtin expressions' % sys._getframe.f_code.co_name)
    return maskSymbBitList


def getPublicSymbList():
    if useBuiltinExp():
        import sys
        print('### Warning: function %s should not be used with builtin expressions' % sys._getframe.f_code.co_name)
    return publicSymbList


def getPublicSymbBitList():
    if useBuiltinExp():
        import sys
        print('### Warning: function %s should not be used with builtin expressions' % sys._getframe.f_code.co_name)
    return publicSymbBitList


def getBitVec(name):
    return symbName2BitVec[name]


def getBitBitVec(name):
    return symbName2BitBitVec[name]


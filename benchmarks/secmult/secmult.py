# Copyright (C) 2019, Sorbonne Universite, LIP6
# This file is part of the SELA project, under the GPL v3.0 license
# See https://www.gnu.org/licenses/gpl-3.0.en.html for license information
# SPDX-License-Identifier: GPL-3.0-only
# Author(s): Quentin L. Meunier

from sela import *

import sys

doUserSimplif = True

def mySimplify(e):
    if doUserSimplif:
        return simp(e)
    else:
        return e

nbExps = 0
nbLeak = 0


def checkExpLeakage(e):
    global nbExps
    global nbLeak
    #print('# checkExpLeakage: %s' % e)
    res, usedBitExp, niTime = checkNIVal(e)
    nbExps += 1
    if not res:
        nbLeak += 1

    #if not res:
    #    print('# Leakage in value for exp num %d: %s' % (nbExps, e))
    #    sys.exit(1)


def gmul(a, b):
    p = constant(0, 8) # the product of the multiplication
    for i in range(8):
        # p = (((unsigned char) (((signed char) ((b & 1) << 7)) >> 7)) & a) ^ p;
        e0 = b & constant(1, 8)
        e0 = mySimplify(e0)
        checkExpLeakage(e0)
        e1 = e0 << 7
        e1 = mySimplify(e1)
        checkExpLeakage(e1)
        e2 = e1 >> 7
        e2 = mySimplify(e2)
        checkExpLeakage(e2)
        e3 = e2 & a
        e3 = mySimplify(e3)
        checkExpLeakage(e3)
        e4 = e3 ^ p
        e4 = mySimplify(e4)
        checkExpLeakage(e4)
        p = e4

        # a = (a << 1) ^ (((unsigned char) (((signed char) (a & 0x80)) >> 7)) & 0x11b);
        e0 = a << 1
        e0 = mySimplify(e0)
        checkExpLeakage(e0)
        e1 = a & constant(0x80, 8)
        e1 = mySimplify(e1)
        checkExpLeakage(e1)
        e2 = e1 >> 7
        e2 = mySimplify(e2)
        checkExpLeakage(e2)
        e3 = e2 & constant(0x1b, 8)
        e3 = mySimplify(e3)
        checkExpLeakage(e3)
        e4 = e0 ^ e3
        e4 = mySimplify(e4)
        checkExpLeakage(e4)
        a = e4

        # b >>= 1;
        e0 = b >> 1
        e0 = mySimplify(e0)
        checkExpLeakage(e0)
        b = e0

    return p



def secmult():

    testLitteral = False

    if not testLitteral:
        m0 = symbol('m0', 'M', 8)
        m1 = symbol('m1', 'M', 8)
        m01 = symbol('m01', 'M', 8)

        k0 = symbol('k0', 'S', 8)
        k1 = symbol('k1', 'S', 8)
    else:
        m0 = constant(0xb9, 8)
        m1 = constant(0x66, 8)
        m01 = constant(0x37, 8)

        k0 = constant(0xa1, 8)
        k1 = constant(0x0f, 8)

    
    a1 = m0 ^ k0
    b1 = m1 ^ k1

    # start analysis
    
    e0 = m01 ^ gmul(m0, b1)
    e0 = mySimplify(e0)
    checkExpLeakage(e0)
    e1 = gmul(a1, m1)
    e1 = mySimplify(e1)
    checkExpLeakage(e1)
    m10 = e0 ^ e1
    m10 = mySimplify(m10)
    checkExpLeakage(m10)

    c0 = gmul(m0, m1)
    c0 = mySimplify(c0)
    checkExpLeakage(c0)
    c0 = c0 ^ m01
    c0 = mySimplify(c0)
    checkExpLeakage(c0)

    c1 = gmul(a1, b1)
    c1 = mySimplify(c1)
    checkExpLeakage(c1)
    c1 = c1 ^ m10
    c1 = mySimplify(c1)
    checkExpLeakage(c1)

    # end analysis

    if testLitteral:
        print('c0 = 0x%x' % int(str(c0)))
        print('c1 = 0x%x' % int(str(c1)))
        print('c0 ^ c1 = 0x%x' % (int(str(simp(c0 ^ c1)))))
        print('k0 * k1 = 0x%x' % (int(str(gmul(k0, k1)))))


if __name__ == '__main__':
    if useBuiltinExp():
        print('SELA')
    else:
        print('SELA Z3')
    import timeit
    for strategy in ['START', 'REPLACE', 'START_REPLACE', 'FAIL', 'START_FAIL', 'FAIL_REPLACE', 'NONE', 'FAIL_1']:
        setSimplifyStrategy(strategy)
        nbExps = 0
        nbLeak = 0
        startTime = timeit.default_timer()
        secmult()
        endTime = timeit.default_timer()
        duration = endTime - startTime
        print('# Strategy [%s]: %3d leakage found / %4d instructions [time = %fs]' % (strategy, nbLeak, nbExps, duration))
    print('# DEACTIVATING USER SIMPLIF')
    doUserSimplif = False
    for strategy in ['FAIL_1', 'NONE']:
        setSimplifyStrategy(strategy)
        nbExps = 0
        nbLeak = 0
        startTime = timeit.default_timer()
        secmult()
        endTime = timeit.default_timer()
        duration = endTime - startTime
        print('# Strategy [%s]: %3d leakage found / %4d instructions [time = %fs]' % (strategy, nbLeak, nbExps, duration))



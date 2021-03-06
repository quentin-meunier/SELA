# Copyright (C) 2019, Sorbonne Universite, LIP6
# This file is part of the SELA project, under the GPL v3.0 license
# See https://www.gnu.org/licenses/gpl-3.0.en.html for license information
# SPDX-License-Identifier: GPL-3.0-only
# Author(s): Quentin L. Meunier

from sela import *

def mySimplify(e):
    if True:
        return simp(e)
    else:
        return e

nbExps = 0
nbLeak = 0

firstOrder = False
secondOrder = True

def checkExpLeakageFirstOrder(e0):
    global nbExps
    global nbLeak
    #print('# checkExpLeakage: %s' % e)
    res, usedBitExp, niTime = checkNIVal(e0)
    nbExps += 1
    if not res:
        nbLeak += 1

    if not res:
        print('# Leakage in value for exp num %d' % (nbExps))


def checkExpLeakageSecondOrder(e0, e1):
    global nbExps
    global nbLeak
    #print('# checkExpLeakage: %s' % e)
    res, usedBitExp, niTime = checkNITrans(e0, e1)
    nbExps += 1
    if not res:
        nbLeak += 1

    if not res:
        print('# Leakage in value for exp num %d' % (nbExps))



def isw_and_3s_norand(m0, m1, m2, m3, z12, z13, z23, k0, k1):
    global nbExps
    global nbLeak

    # computing shares
    a1 = m0
    a2 = m1
    a3 = m0 ^ m1 ^ k0

    b1 = m2
    b2 = m3
    b3 = m2 ^ m3 ^ k1;

    signals = []
    signals.append(a1)
    signals.append(a2)
    signals.append(a3)
    signals.append(b1)
    signals.append(b2)
    signals.append(b3)

    # output c = c1 ^ c2 ^ c3 = a & b

    # start analysis
    a1b1 = a1 & b1
    a1b1 = mySimplify(a1b1)
    signals.append(a1b1)

    a1b2 = a1 & b2
    a1b2 = mySimplify(a1b2)
    signals.append(a1b2)

    a1b3 = a1 & b3
    a1b3 = mySimplify(a1b3)
    signals.append(a1b3)


    a2b1 = a2 & b1
    a2b1 = mySimplify(a2b1)
    signals.append(a2b1)

    a2b2 = a2 & b2
    a2b2 = mySimplify(a2b2)
    signals.append(a2b2)

    a2b3 = a2 & b3
    a2b3 = mySimplify(a2b3)
    signals.append(a2b3)


    a3b1 = a3 & b1
    a3b1 = mySimplify(a3b1)
    signals.append(a3b1)

    a3b2 = a3 & b2
    a3b2 = mySimplify(a3b2)
    signals.append(a3b2)

    a3b3 = a3 & b3
    a3b3 = mySimplify(a3b3)
    signals.append(a3b3)


    z21i = z12 ^ a1b2
    z21i = mySimplify(z21i)
    signals.append(z21i)

    z21 = z21i ^ a2b1
    z21 = mySimplify(z21)
    signals.append(z21)

    z31i = z13 ^ a1b3
    z31i = mySimplify(z31i)
    signals.append(z31i)

    z31 = z31i ^ a3b1
    z31 = mySimplify(z31)
    signals.append(z31)

    z32i = z23 ^ a2b3
    z32i = mySimplify(z32i)
    signals.append(z32i)

    z32 = z32i ^ a3b2
    z32 = mySimplify(z32)
    signals.append(z32)


    c1i = a1b1 ^ z12
    c1i = mySimplify(c1i)
    signals.append(c1i)

    c1 = c1i ^ z13
    c1 = mySimplify(c1)
    signals.append(c1)

    c2i = a2b2 ^ z21
    c2i = mySimplify(c2i)
    signals.append(c2i)

    c2 = c2i ^ z23
    c2 = mySimplify(c2)
    signals.append(c2)

    c3i = a3b3 ^ z31
    c3i = mySimplify(c3i)
    signals.append(c3i)

    c3 = c3i ^ z32
    c3 = mySimplify(c3)
    signals.append(c3)


    if firstOrder:
        print('# First Order Analysis')
        for s0idx in range(len(signals)):
            checkExpLeakageFirstOrder(signals[s0idx])

        print('# Nb. expressions analysed: %d' % nbExps)
        print('# Nb. expressions leaking: %d' % nbLeak)



    if secondOrder:
        nbExps = 0
        nbLeak = 0
        print('# Second Order Analysis')
        for s0idx in range(len(signals)):
            for s1idx in range(s0idx + 1, len(signals)):
                checkExpLeakageSecondOrder(signals[s0idx], signals[s1idx])

        print('# Nb. expressions analysed: %d' % nbExps)
        print('# Nb. expressions leaking: %d' % nbLeak)


    return c1, c2, c3




if __name__ == '__main__':

    testLitteral = False

    if not testLitteral:
        m0 = symbol('m0', 'M', 1)
        m1 = symbol('m1', 'M', 1)
        m2 = symbol('m2', 'M', 1)
        m3 = symbol('m3', 'M', 1)

        z12 = symbol('z12', 'M', 1)
        z13 = symbol('z13', 'M', 1)
        z23 = symbol('z23', 'M', 1)

        k0 = symbol('k0', 'S', 1)
        k1 = symbol('k1', 'S', 1)

        c1, c2, c3 = isw_and_3s_norand(m0, m1, m2, m3, z12, z13, z23, k0, k1)

    else:
        def enumerate_values(t, currIdx):
            if currIdx == len(t):
                m0 = constant(t[0], 1)
                m1 = constant(t[1], 1)
                m2 = constant(t[2], 1)
                m3 = constant(t[3], 1)
                z12 = constant(t[4], 1)
                z13 = constant(t[5], 1)
                z23 = constant(t[6], 1)
                k0 = constant(t[7], 1)
                k1 = constant(t[8], 1)

                c1, c2, c3 = isw_and_3s_norand(m0, m1, m2, m3, z12, z13, z23, k0, k1)
 
                r_ref = k0 & k1
                r_ref = mySimplify(r_ref)
                r = c1 ^ c2 ^ c3
                r = mySimplify(r)

                # Comparing strings ('0' or '1')  because of the two different implementations (either use 'is' or '==')
                if '%s' % r_ref != '%s' % r:
                    print('*** Error for values (%s, %s, %s, %s, %s, %s, %s, %s, %s): result is %s instead of %s' % (m0, m1, m2, m3, z12, z13, z23, k0, k1, r, r_ref))
                    sys.exit(0)
            else:
                t[currIdx] = 0
                enumerate_values(t, currIdx + 1)
                t[currIdx] = 1
                enumerate_values(t, currIdx + 1)

        t = [0] * 9
        enumerate_values(t, 0)
        print('[OK]')



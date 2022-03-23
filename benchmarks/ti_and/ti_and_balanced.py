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


firstOrder = True
secondOrder = False

def checkExpLeakageFirstOrder(e0):
    global nbExps
    global nbLeak
    #print('# checkExpLeakage: %s' % e0)
    res, usedBitExp, niTime = checkNIVal(e0)
    nbExps += 1
    if not res:
        nbLeak += 1

    if not res:
        print('# Leakage exp num %d' % (nbExps))


def checkExpLeakageSecondOrder(e0, e1):
    global nbExps
    global nbLeak
    #print('# checkExpLeakage: (%s, %s)' % (e0, e1))
    res, usedBitExp, niTime = checkNITrans(e0, e1)
    nbExps += 1
    if not res:
        nbLeak += 1

    if not res:
        print('# Leakage for exp num %d' % (nbExps))



def ti_and_balanced(m0, m1, m2, m3, m4, m5, k0, k1):
    global nbExps
    global nbLeak

    # computing shares
    x1 = m0
    x2 = m1
    x3 = m2
    x4 = m0 ^ m1 ^ m2 ^ k0

    y1 = m3
    y2 = m4
    y3 = m5
    y4 = m3 ^ m4 ^ m5 ^ k1;

    signals = []
    signals.append(x1)
    signals.append(x2)
    signals.append(x3)
    signals.append(x4)
    signals.append(y1)
    signals.append(y2)
    signals.append(y3)
    signals.append(y4)

    # output z = z1 ^ z2 ^ z3 ^ z4 = x & y

    x3_x4 = x3 ^ x4
    x3_x4 = mySimplify(x3_x4)
    signals.append(x3_x4)

    y2_y3 = y2 ^ y3
    y2_y3 = mySimplify(y2_y3)
    signals.append(y2_y3)

    t0 = x3_x4 & y2_y3
    t0 = mySimplify(t0)
    signals.append(t0)

    t1 = t0 ^ y2
    t1 = mySimplify(t1)
    signals.append(t1)

    t2 = t1 ^ y3
    t2 = mySimplify(t2)
    signals.append(t2)

    t3 = t2 ^ y4
    t3 = mySimplify(t3)
    signals.append(t3)

    t4 = t3 ^ x2
    t4 = mySimplify(t4)
    signals.append(t4)

    t5 = t4 ^ x3
    t5 = mySimplify(t5)
    signals.append(t5)

    z1 = t5 ^ x4
    z1 = mySimplify(z1)
    signals.append(z1)



    x1_x3 = x1 ^ x3
    x1_x3 = mySimplify(x1_x3)
    signals.append(x1_x3)

    y1_y4 = y1 ^ y4
    y1_y4 = mySimplify(y1_y4)
    signals.append(y1_y4)

    t0 = x1_x3 & y1_y4
    t0 = mySimplify(t0)
    signals.append(t0)

    t1 = t0 ^ y1
    t1 = mySimplify(t1)
    signals.append(t1)

    t2 = t1 ^ y3
    t2 = mySimplify(t2)
    signals.append(t2)

    t3 = t2 ^ y4
    t3 = mySimplify(t3)
    signals.append(t3)

    t4 = t3 ^ x1
    t4 = mySimplify(t4)
    signals.append(t4)

    t5 = t4 ^ x3
    t5 = mySimplify(t5)
    signals.append(t5)

    z2 = t5 ^ x4
    z2 = mySimplify(z2)
    signals.append(z2)



    x2_x4 = x2 ^ x4
    x2_x4 = mySimplify(x2_x4)
    signals.append(x2_x4)

    t0 = x2_x4 & y1_y4
    t0 = mySimplify(t0)
    signals.append(t0)

    t1 = t0 ^ y2
    t1 = mySimplify(t1)
    signals.append(t1)

    z3 = t1 ^ x2
    z3 = mySimplify(z3)
    signals.append(z3)



    x1_x2 = x1 ^ x2
    x1_x2 = mySimplify(x1_x2)
    signals.append(x1_x2)

    t0 = x1_x2 & y2_y3
    t0 = mySimplify(t0)
    signals.append(t0)

    t1 = t0 ^ y1
    t1 = mySimplify(t1)
    signals.append(t1)

    z4 = t1 ^ x1
    z4 = mySimplify(z4)
    signals.append(z4)


    if firstOrder:
        nbExps = 0
        nbLeak = 0
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


    return z1, z2, z3, z4




if __name__ == '__main__':

    testLitteral = False

    if not testLitteral:
        m0 = symbol('m0', 'M', 1)
        m1 = symbol('m1', 'M', 1)
        m2 = symbol('m2', 'M', 1)
        m3 = symbol('m3', 'M', 1)
        m4 = symbol('m4', 'M', 1)
        m5 = symbol('m5', 'M', 1)

        k0 = symbol('k0', 'S', 1)
        k1 = symbol('k1', 'S', 1)

        z1, z2, z3, z4 = ti_and_balanced(m0, m1, m2, m3, m4, m5, k0, k1)

    else:
        def enumerate_values(t, currIdx):
            if currIdx == len(t):
                m0 = constant(t[0], 1)
                m1 = constant(t[1], 1)
                m2 = constant(t[2], 1)
                m3 = constant(t[3], 1)
                m4 = constant(t[4], 1)
                m5 = constant(t[5], 1)
                k0 = constant(t[6], 1)
                k1 = constant(t[7], 1)

                z1, z2, z3, z4 = ti_and_balanced(m0, m1, m2, m3, m4, m5, k0, k1)
 
                r_ref = k0 & k1
                r_ref = mySimplify(r_ref)
                r = z1 ^ z2 ^ z3 ^ z4
                r = mySimplify(r)

                # Comparing strings ('0' or '1')  because of the two different implementations (either use 'is' or '==')
                if '%s' % r_ref != '%s' % r:
                    print('*** Error for values (%s, %s, %s, %s, %s, %s, %s, %s): result is %s instead of %s' % (m0, m1, m2, m3, m4, m5, k0, k1, r, r_ref))
                    sys.exit(0)
            else:
                t[currIdx] = 0
                enumerate_values(t, currIdx + 1)
                t[currIdx] = 1
                enumerate_values(t, currIdx + 1)

        t = [0] * 8
        enumerate_values(t, 0)
        print('[OK]')



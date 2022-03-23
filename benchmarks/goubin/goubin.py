# Copyright (C) 2019, Sorbonne Universite, LIP6
# This file is part of the SELA project, under the GPL v3.0 license
# See https://www.gnu.org/licenses/gpl-3.0.en.html for license information
# SPDX-License-Identifier: GPL-3.0-only
# Author(s): Quentin L. Meunier

from sela import *

# secret : k
# masks : m, n


def mySimplify(e):
    if True:
        return simp(e)
    else:
        return e

numExps = 0
numLeak = 0

def checkExpLeakage(e):
    global numExps
    global numLeak
    numExps += 1

    res, usedBitExp, niTime = checkNIVal(e)
    if not res:
        numLeak += 1
    if not res:
        print('# Leakage in value for exp %s' % e)
    #else:
    #    if usedBitExp:
    #        print('# used bit exp')
    #    else:
    #        print('# did not use bit exp')


def booleanToArithmetic(xp, m, n):
    t = xp ^ n
    t = mySimplify(t)
    checkExpLeakage(t)
    t = t - n
    t = mySimplify(t)
    checkExpLeakage(t)
    t = t ^ xp
    t = mySimplify(t)
    checkExpLeakage(t)
    n = n ^ m
    n = mySimplify(n)
    checkExpLeakage(n)
    a = xp ^ n
    a = mySimplify(a)
    checkExpLeakage(a)
    a = a - n
    a = mySimplify(a)
    checkExpLeakage(a)
    a = a ^ t
    a = mySimplify(a)
    checkExpLeakage(a)
    return a


if __name__ == '__main__':
    k = symbol('k', 'S', 8)
    m = symbol('m', 'M', 8)
    n = symbol('n', 'M', 8)
    
    xp = k ^ m
    # start analysis
    a = booleanToArithmetic(xp, m, n)
    # end analysis
    print('# Nb. expressions analysed: %d' % numExps)
    print('# Nb. expressions leaking: %d' % numLeak)




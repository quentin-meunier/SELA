#!/usr/bin/python

# Copyright (C) 2019, Sorbonne Universite, LIP6
# This file is part of the SELA project, under the GPL v3.0 license
# See https://www.gnu.org/licenses/gpl-3.0.en.html for license information
# SPDX-License-Identifier: GPL-3.0-only
# Author(s): Quentin L. Meunier

from __future__ import print_function

from secmult import *
from topcell import *

instList = getGeneratedInsts()

topcell = Topcell(instList, getStartAddress(), getStopAddress(), getRegisterInit(), setGeneratedMemory)

cycle = 0
while True:
    print('### Cycle %3d ###' % cycle)
    cycle += 1

    stop = topcell.advanceCycle()
    if stop:
        break
    topcell.computeOutput()
    topcell.analyse()

topcell.displayResults()


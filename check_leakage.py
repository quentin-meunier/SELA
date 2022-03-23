#!/usr/bin/python

# Copyright (C) 2019, Sorbonne Universite, LIP6
# This file is part of the SELA project, under the GPL v3.0 license
# See https://www.gnu.org/licenses/gpl-3.0.en.html for license information
# SPDX-License-Identifier: GPL-3.0-only
# Author(s): Quentin L. Meunier


from __future__ import print_function
import timeit

from ni import *
from exp import *
from config import *


if useBuiltinExp():
    from check_leakage_be import *
else:
    from check_leakage_z3 import *


def checkNIVal(e):
    return checkNIVal_(e)

def checkNITrans(exp0, exp1):
    return checkNITrans_(exp0, exp1)

def checkNITransXor(exp0, exp1):
    return checkNITransXor_(exp0, exp1)

def checkNITransBit(exp0, exp1):
    return checkNITransBit_(exp0, exp1)

def checkNITransXorBit(exp0, exp1):
    return checkNITransXorBit_(exp0, exp1)


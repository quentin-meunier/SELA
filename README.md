# SELA: a Symbolic Expression Leakage Analyzer

SELA is a formal verification tool for the probing security of masked implementations. It provides a way for verifying probing security on a set of symbolic expressions.

SELA is a python library offering a set of constructs and functions for writing and verifying symbolic expressions. A symbolic expression in SELA is a fixed width expression comprising operations on constants and symbolic variables. Each symbolic variable has a type between secret, mask and public. SELA verifies that the distribution of the expression value is independent from the secret values it contains, considering that mask variables follow an random uniform distribution.

This work has been published under the following reference:  
Meunier, Q. L., El Ouahma, I. B., & Heydemann, K. (2020, September). SELA: a Symbolic Expression Leakage Analyzer. In International Workshop on Security Proofs for Embedded Systems.
[Link](https://hal.archives-ouvertes.fr/hal-02983213/)

SELA is the ancestor of [LeakageVerif](https://github.com/quentin-meunier/LeakageVerif).


## Installation

As a python library, SELA only needs to be cloned to a directory called `sela`, which is the name of the python module it provides. The parent directory of `leakage_verif` must be added to the PYTHONPATH environment variable. SELA has two expression representations: one using internal SELA expressions, and one using the python z3 front-end (z3py) expressions. In order to use those, z3 python module must be installed as well. Using z3 expessions provides better results in some cases, as illustrated in the article. This can be made by setting the variable `builtinExp` to `False` in the `config.py` file.


## Usage

In order to use SELA constructs, put the following line at the beginning of a python file:
```
from sela import *
```

Symbolic variables are created with a function called `symbol`: the first parameter is the symbol name, the second parameter the symbol type ('S' for secret, 'M' for mask and 'P' for a public variable), and the third parameter the symbol width. Constants with a function called `constant`, taking as parameters the value and the width.
```
from __future__ import print_function
from sela import *

# Creating an 8-bit secret variable named 'k' 
k = symbol('k', 'S', 8)

# Creating an 8-bit mask variable named 'm0'
m = symbol('m', 'M', 8)

# Creating the 8-bit constant 0xAE
c = constant(0xAE, 8)

# Computing an expression
e = k ^ m ^ c

# Checking probing security on e
res = checkNIVal(e)

if res[0]:
    print('# Expression %s is probing secure' % e)
else:
    print('# Expression %s is not probing secure' % e)

```

## Supported operations

* `^`: bitwise exclusive OR
* `&`: bitwise AND
* `|`: bitwise OR
* `~`: bitwise NOT
* `+`: arithmetic addition
* `-`: arithmetic subtraction
* `<<`: logical shift left. The shift amount must be a constant or a python integer, and cannot be symbolic.
* `>>`: arithmetic shift right. The shift amount must be a constant or a python integer, and cannot be symbolic.

Some operations are implemented in the form of functions:

* `LShR(x, y)`: logical shift right. The shift amount y must be a constant or a python integer, and cannot be symbolic.
* `Concat(x, y, ...)`: concatenation of expressions
* `Extract(msb, lsb, e)`: extraction of some of the bits in `e`, from the most significant bit given by msb, to the least significant bit given by lsb.
* `ZeroExt(v, e)`: zero extension: extension of the expression `e` by the addition of v bits with value 0 on the left of `e`
* `SignExt(v, e)`: signed extension: extension of the expression `e` by adding v time the MSB of `e` on its left

## Functionalities

### Simplification

SELA implements some simplifications, taking advantage of operators properties. In order to simplify an expression, simply call the `simplify` function:
```
p0 = symbol('p0', 'P', 8)
p1 = symbol('p1', 'P', 8)
m = symbol('m', 'M', 8)
e = ((p0 ^ m) | (p1 & constant(0, 8))) ^ (m & constant(0xFF, 8) + (p0 ^ p0))
simplify(e)
print('simplifiedExp: %s' % e)
```

Several simplification strategies are implemented, and detailed in the article. The default one simplfies an expression at the start of the verification process and after each replacement. The strategy to use can be configured in the `config.py' file.


### Bit decomposition of expressions

SELA uses a double representation for expressions: one using words and one using bits. In some cases, it is advisable to deactivate the bit representation. This can be done by setting to False the variable `bitExp' in the `config.py' file.
```

### Verification

The main verification function, `checkNIVal(e)` verifies the probing security of the expression `e`. Some other security properties are also considered, and are detailed in the article:

* `checkNITrans(e0, e1)`: verifies that the couple of expression (e0, e1) is probing secure
* `checkNITransXor(e0, e1)`: verifies that expression `e0 ^ e1` is probing secure
* `checkNITransBit(e0, e1)`: verifies that each couple of expressions of the form (`e0[i]`, `e1[i]`) is probing secure, where `e0[i]` (resp. `e1[i]`) is the expression of the `i`-th bit of `e0` (resp. `e1`)
* `checkNITransXorBit(e0, e1)`: verifies that each expression of the form `e0[i] ^ e1[i]` is probing secure



## Benchmarks

The `benchmarks` directory contains a few applications.

* Trichina-And: Trichina AND gate with and without additional random [1]
* TI-And: TI AND gate with three (unbalanced) and four (balanced) shares [2]
* GMS-And: GMS AND gate with 3 and 5 shares [3]
* ISW-And: several versions of the ISW AND scheme from [4]. Versions with 2 or 3 shares are considered, as well as the presence of an additional random for computing expression of the form a<sub>i</sub>b<sub>j</sub>. Verifications are made at the first and second orders.
* Secmult: secure Galois field multiplication as described in [5].
* Arm-Asm: Arm assembly implementations of the Secmult program. Minimal models for the ISA and the memory are provided, and the leakage model consists in analyzing the result (value) of each instruction which modifies a general purpose register in the processor core.



## License

[GPLv3](https://www.gnu.org/licenses/gpl-3.0.en.html)



## References

[1] Trichina, E. (2003). Combinational logic design for AES subbyte transformation on masked data. Cryptology EPrint Archive.

[2] Nikova, S., Rechberger, C., & Rijmen, V. (2006, December). Threshold implementations against side-channel attacks and glitches. In International conference on information and communications security (pp. 529-545). Springer, Berlin, Heidelberg. 

[3] Reparaz, O., Bilgin, B., Nikova, S., Gierlichs, B., & Verbauwhede, I. (2015, August). Consolidating masking schemes. In Annual Cryptology Conference (pp. 764-783). Springer, Berlin, Heidelberg.

[4] Ishai, Y., Sahai, A., and Wagner, D. (2003, August). Private circuits: Securing hardware against probing attacks. In Annual International Cryptology Conference (pp. 463-481). Springer, Berlin, Heidelberg.

[5] Rivain, M., and Prouff, E. (2010, August). Provably secure higher-order masking of AES. In International Workshop on Cryptographic Hardware and Embedded Systems (pp. 413-427). Springer, Berlin, Heidelberg.


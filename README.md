# halo2-coprime

A Halo2 config for verifiable computation of a greatest common denominator (GCD) and least common factor (LCM) between two integers through Euclid's algorithm. It constrains each column to be a valid Euclid algorithm transition and allows to publicly expose the result. It can be useful in cryptosystems requiring coprimes, such as the Paillier homomorphic cryptosystem. 
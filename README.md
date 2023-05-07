# halo2-coprime

A Halo2 config for verifiable computation of a greatest common denominator (GCD) and least common factor (LCM) between two integers through Euclid's algorithm. It constrains each column to be a valid Euclid algorithm transition and allows to publicly expose the result, or to constrain it to 1. This can be useful in cryptosystems requiring coprimes, such as the Paillier homomorphic cryptosystem. 

To calculate the GCD, we use a modified version of Euclid's algorithm to check the GCD. The original algorithm is as follows:

| col_a     | col_b     |
|:---------:|:---------:|
| a         | b         | 
| b         | a%b       |
| ...       | ...       |
| gcd(a,b)  | 0         |

However, because moduli and integer divisions cannot be represented as polynomial constraints over fields, we have to introduce $a//b$, the integer division of $a$ by $b$, and constrain the values using the relationship $a = (a//b) * b + a\%b$. We also enforce that none of these values can exceed $sqrt(p)$ using a lookup, to prevent overflows. With some packing, we arrive to the following configuration:

| col_a     | col_b     | q_euclid_init | q_euclid_ss | q_gcd | q_coprime | q_lookup |
|:---------:|:---------:|:-------------:|:-----------:|:-----:|:---------:|:--------:|
| $a$       | $b$       | 0             | 0           | 0     | 0         | 1        |
| $a//b$    | $a\%b$    | 1             | 0           | 0     | 0         | 1        |
| $b//(a\%b)$| $b\%(a\%b)$ | 0             | 1           | 0     | 0         | 1        |
| ...       | ...       | 0             | 1           | 0     | 0         | 1        |
| x         | $gcd(a, b)$| 0             | 1           | 0     | 0         | 1        |
| x         | $0$       | 0             | 1           | 1     | 0/1       | 1        |

Here, we initialize our columns with $a$, $b$, $a//b$ and $a\%b$ on the first two rows. We enforce the aforementioned constraint through the $q_{euclid\_init}$ selector. After this, we apply the steady-state constraint ($b_{i-2} = b_{i-1} * a_i + b_i$) to all subsequent rows through the $q_{euclid\_ss}$ selector. This algorithm will always end with a $0$ in the $b$ column, and this will indicate that the GCD has been reached in the previous $b$. We constrain that we've reached the end through the $q_{gcd}$ selector by enforcing these properties. The $q_{coprime}$ selector constrains the GCD to $1$. 
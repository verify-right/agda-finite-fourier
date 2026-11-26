# Fourier transforms on product groups

Consider the group $C_2\times C_2$ over $\mathbb{F}_{17}$.

The two-point Fourier matrix is

$$
K=\begin{pmatrix}1&1\\1&-1\end{pmatrix}.
$$

The product character table is the Kronecker product

$$
K\otimes K=
\begin{pmatrix}
1&1&1&1\\
1&-1&1&-1\\
1&1&-1&-1\\
1&-1&-1&1
\end{pmatrix}.
$$

This is the Walsh–Hadamard transform.

## Transforming along each axis

Take the input

$$
A=\begin{pmatrix}0&1\\2&3\end{pmatrix}.
$$

Transform each row:

$$
AK^T=\begin{pmatrix}1&-1\\5&-1\end{pmatrix}.
$$

Then transform each column:

$$
KAK^T=\begin{pmatrix}6&-2\\-4&0\end{pmatrix}.
$$

Modulo 17, the resulting vector is $(6,15,13,0)$.

The theorem `Tables.factorization` proves that successive
axis transforms agree with the full product transform.

[Agda proofs](../src/Fourier/ProductTable.agda).

# Autocorrelation and flat spectra

For a cyclic signal $f$, define its autocorrelation by

$$
C(t)=\sum_x f(x)f(x-t).
$$

By the convolution theorem and reindexing under negation,

$$
\widehat C(\chi)=\widehat f(\chi)\widehat f(\chi^{-1}).
$$

[Autocorrelation.agda](../src/Fourier/Autocorrelation.agda) proves this for finite enumerated abelian groups. With real signals and unitary complex characters the product is the squared spectral magnitude.

## Two-level correlation

Suppose $C(t)=b+s\delta_{0t}$. The same `two-level` lemma used for weighted character sums gives

$$
\widehat C(\chi)=b\sum_t\chi(t)+s.
$$

For the row $(1,1,1,-1)$, the cyclic correlation is $(4,0,0,0)$. Every character reads out 4. In particular the constant character gives $(1+1+1-1)^2=4$.

[FlatSpectrum.agda](../src/Fourier/FlatSpectrum.agda) proves the generic identity and its impulse and row-sum corollaries. [IntegerCorrelationExamples.agda](../src/Fourier/IntegerCorrelationExamples.agda) checks the four-point example over the integers and derives the row-sum square for any positive cyclic length with the stated impulse correlation. Neither inverse transforms nor sign constraints are required.

This is the elementary augmentation constraint used in the OpenAI circulant Hadamard development: [CyclicNorm.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/CirculantHadamard/CyclicNorm.lean#L136), `augmentation_sum_sq_of_norm`. Compare [CyclicEvaluation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/CirculantHadamard/CyclicEvaluation.lean#L113), `evaluate_norm_eq`. The matrix-to-correlation equivalence and subsequent descent are not proved here. For the connection with difference sets, see [Turyn (1965)](https://msp.org/pjm/1965/15-1/pjm-v15-n1-p32-s.pdf).

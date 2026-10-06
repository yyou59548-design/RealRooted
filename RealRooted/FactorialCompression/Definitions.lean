import RealRooted.FactorialCompression.Internal.Multiplier
import RealRooted.FactorialCompression.Internal.Kernels

/-! Exact definitions from the authoritative 19-page final manuscript,
equations (1.1), (3.4), (3.5). The finite-sum extension has the manuscript
domain degree at most N; theorem statements retain that domain explicitly. -/

open Polynomial
open scoped BigOperators

noncomputable section
namespace RealRooted.FactorialCompression

def mu (N ell k : ℕ) : ℝ :=
  if 2 * k ≤ N + ell then
    (Nat.factorial (N - k) : ℝ) / (Nat.factorial (N + ell - 2 * k) : ℝ)
  else 0

def compression (N ell : ℕ) (p : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (N + 1), C (mu N ell k * p.coeff k) * X ^ k

def nextPolynomial (a : ℝ) (p : ℝ[X]) : ℝ[X] :=
  (X + C a) * p + X * p.derivative

def alpha (N ell : ℕ) (a : ℝ) : ℝ :=
  1 / 4 + a * ((N : ℝ) + 1) /
    (((N + ell : ℕ) : ℝ) * (((N + ell : ℕ) : ℝ) + 1))

def beta (N ell : ℕ) (a : ℝ) : ℝ :=
  ((N : ℝ) - (ell : ℝ) + 1) *
    (1 / 2 + a / (((N + ell : ℕ) : ℝ) + 1))

def kernel (N ell : ℕ) (a : ℝ) : ℝ[X] :=
  C (alpha N ell a) * RealRooted.FactorialCompression.Internal.h (N + ell) +
    (C (beta N ell a) * X - C (1 / 4 : ℝ)) *
      RealRooted.FactorialCompression.Internal.h (N + ell - 1)

end RealRooted.FactorialCompression

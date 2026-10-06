import RealRooted.FactorialCompression.Internal.Conventions

/- Exact finite sums for manuscript (2.2), (3.4), (3.5), (4.1), (4.3), (4.5).
Compression and multiplier have domain degree at most N in the manuscript;
their finite-sum extensions below agree on that domain. No preservation or
interlacing theorem is asserted by these definitions. -/

open Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.FactorialCompression.Internal

def mu (N k : ℕ) : ℝ :=
  if 2 * k ≤ N + 1 then
    (Nat.factorial (N - k) : ℝ) / (Nat.factorial (N + 1 - 2 * k) : ℝ)
  else 0

def compression (N : ℕ) (p : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (N + 1), C (mu N k * p.coeff k) * X ^ k

def finiteMultiplier (N : ℕ) (p f : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (N + 1),
    C (p.coeff k / (Nat.choose N k : ℝ) * f.coeff k) * X ^ k

def nextPolynomial (N : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (X + C (((N : ℝ) + 2) / 2)) * p + X * p.derivative

def B : ℕ → ℝ[X]
  | 0 => 1
  | N + 1 => nextPolynomial N (B N)

def h (r : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (r / 2 + 1),
    C ((Nat.factorial r : ℝ) /
      ((Nat.factorial j : ℝ) * (Nat.factorial (r - 2 * j) : ℝ))) * X ^ j

def kernel (N : ℕ) : ℝ[X] :=
  C (3 / 4 : ℝ) * h (N + 1) +
    (C (N : ℝ) * X - C (1 / 4 : ℝ)) * h N

end RealRooted.FactorialCompression.Internal

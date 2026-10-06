import RealRooted.Basic.ProperPosition

/-
The manuscript uses strict inequalities between its ordered root lists.
The upstream name StrictInterl uses weak inequalities. These definitions
retain the manuscript's inequalities; the one-way bridge loses strictness
and is only an API adapter, never a replacement for a manuscript theorem.
The build logs and status ledger record checks in the required pinned environment.
-/

open Polynomial

noncomputable section

namespace RealRooted.FactorialCompression.Internal

/-- Root order (1.2), with the constant/linear base convention. -/
def StrictInterlacesRoots : List ℝ → List ℝ → Prop
  | [], [] => True
  | [], [_] => True
  | r :: rs, s₁ :: s₂ :: ss =>
      s₁ < r ∧ r < s₂ ∧ StrictInterlacesRoots rs (s₂ :: ss)
  | _, _ => False

/-- Root order (1.3). -/
def StrictAlternatesRoots : List ℝ → List ℝ → Prop
  | [], [] => True
  | r :: rs, s :: ss => r < s ∧ StrictInterlacesRoots rs (s :: ss)
  | _, _ => False

/-- A polynomial's complete root multiset consists of simple negative roots.
Splitting and nonzeroness exclude vacuous statements about missing real roots. -/
def SimpleNegativeRoots (p : ℝ[X]) : Prop :=
  p ≠ 0 ∧ p.Splits ∧ p.roots.Nodup ∧ ∀ r ∈ p.roots, r < 0

/-- The strict oriented polynomial root orders in the manuscript.
The leading signs, splitting and strictly ordered full root lists are explicit. -/
def ManuscriptStrictInterl (f g : ℝ[X]) : Prop :=
  0 < f.leadingCoeff ∧ 0 < g.leadingCoeff ∧ f.Splits ∧ g.Splits ∧
    ∃ rs ss : List ℝ,
      rs.Pairwise (· < ·) ∧ ss.Pairwise (· < ·) ∧
      (↑rs : Multiset ℝ) = f.roots ∧ (↑ss : Multiset ℝ) = g.roots ∧
      ((rs.length + 1 = ss.length ∧ StrictInterlacesRoots rs ss) ∨
        (rs.length = ss.length ∧ StrictAlternatesRoots rs ss))

theorem strictInterlacesRoots_to_upstream :
    ∀ {rs ss : List ℝ}, StrictInterlacesRoots rs ss →
      RealRooted.ListInterlaces rs ss
  | [], [], _ => True.intro
  | [], [_], _ => True.intro
  | [], _ :: _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h
  | _ :: _, [_], h => False.elim h
  | r :: rs, s₁ :: s₂ :: ss, h =>
      ⟨le_of_lt h.1, le_of_lt h.2.1,
        strictInterlacesRoots_to_upstream h.2.2⟩

theorem strictAlternatesRoots_to_upstream :
    ∀ {rs ss : List ℝ}, StrictAlternatesRoots rs ss →
      RealRooted.ListAlternates rs ss
  | [], [], _ => True.intro
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h
  | _ :: _, _ :: _, h =>
      ⟨le_of_lt h.1, strictInterlacesRoots_to_upstream h.2⟩

end RealRooted.FactorialCompression.Internal

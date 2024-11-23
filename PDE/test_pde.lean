import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Basis.Defs

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- The standard basis vector in direction i for n-dimensional space. -/
def standardBasis (i j : n) : 𝕜 := if i = j then 1 else 0

/-- Partial derivative of a function f at point x in direction i.
    Defined as the line derivative with respect to the standard basis vector eᵢ. -/
noncomputable def partialDeriv (f : (n → 𝕜) → F) (i : n) (x : n → 𝕜) : F :=
  lineDeriv 𝕜 f x (standardBasis i)

/-- A function has a partial derivative at x in direction i if it has a line derivative
    in the direction of the i-th standard basis vector. -/
def HasPartialDerivAt (f : (n → 𝕜) → F) (f' : F) (i : n) (x : n → 𝕜) : Prop :=
  HasLineDerivAt 𝕜 f f' x (standardBasis i)

/-- A function is partially differentiable at x in direction i if it has a line derivative
    in the direction of the i-th standard basis vector. -/
def PartialDifferentiableAt (f : (n → 𝕜) → F) (i : n) (x : n → 𝕜) : Prop :=
  LineDifferentiableAt 𝕜 f x (standardBasis i)

/-- Basic lemmas about partial derivatives -/
theorem partialDeriv_eq_of_hasPartialDerivAt
  {f : (n → 𝕜) → F} {f' : F} {i : n} {x : n → 𝕜}
  (h : HasPartialDerivAt f f' i x) :
  partialDeriv f i x = f' :=
HasLineDerivAt.lineDeriv h

/-- Partial differentiability implies existence of partial derivative -/
theorem partialDifferentiableAt_iff_exists_partialDeriv
  {f : (n → 𝕜) → F} {i : n} {x : n → 𝕜} :
  PartialDifferentiableAt f i x ↔ ∃ f', HasPartialDerivAt f f' i x :=
⟨fun h => ⟨partialDeriv f i x, LineDifferentiableAt.hasLineDerivAt h⟩,
 fun ⟨f', h⟩ => HasLineDerivAt.lineDifferentiableAt h⟩

--Here is an alternate proof which is easy to read 
/-- Partial differentiability implies existence of partial derivative -/
theorem partialDifferentiableAt_iff_exists_partialDeriv
  {f : (n → 𝕜) → F} {i : n} {x : n → 𝕜} :
  PartialDifferentiableAt f i x ↔ ∃ f', HasPartialDerivAt f f' i x :=
  -- This code uses the `split` tactic to split the current goal into multiple subgoals.
  -- It then introduces a hypothesis `h` for each subgoal.
  by
  constructor
  · intro h
    exists (partialDeriv f i x)
    apply LineDifferentiableAt.hasLineDerivAt h
  · intro ⟨f', h⟩
    apply HasLineDerivAt.lineDifferentiableAt h

/-- Uniqueness of partial derivatives when they exist -/
theorem hasPartialDerivAt.unique
  {f : (n → 𝕜) → F} {f₁' f₂' : F} {i : n} {x : n → 𝕜}
  (h₁ : HasPartialDerivAt f f₁' i x)
  (h₂ : HasPartialDerivAt f f₂' i x) :
  f₁' = f₂' :=
HasLineDerivAt.unique h₁ h₂

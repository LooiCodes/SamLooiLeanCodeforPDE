import Mathlib.Topology.MetricSpace.Lipschitz  -- For HolderWith, HolderOnWith
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs


set_option diagnostics true
set_option diagnostics.threshold 30000
set_option linter.unusedVariables false

/-!
# Hölder Spaces

Building on Mathlib's existing definitions of Hölder continuity, we define:
- The Hölder norm (combining C⁰ norm and Hölder seminorm)
- Hölder spaces C^{k,γ}
- The Banach space structure on Hölder spaces

Main definitions from Mathlib we'll use:
- `HolderWith C γ f` : f is γ-Hölder continuous with constant C
- `HolderOnWith C γ f s` : f is γ-Hölder continuous on set s with constant C
-/

variable {Y: Type*}

open Filter Set

open NNReal Real ENNReal Topology

variable [PseudoMetricSpace Y]

namespace HolderSpace

abbrev Euc 𝕜 n := EuclideanSpace 𝕜 (Fin n)

abbrev X n := Euc ℝ n

/-- A function `f : U <= subset of R^n → Y` between two `PseudoEMetricSpace`s is Hölder continuous with constant
`C : ℝ≥0` and exponent `r : ℝ≥0`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y : X`. -/
def HolderWith (n:  ℕ) (C r : ℝ≥0) (f : X n → Y) : Prop :=
  ∀ x y, edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y ^ (r : ℝ)

/-- The C⁰ norm (supremum norm) of a bounded continuous function -/
noncomputable def normC0 (n : ℕ)
  (f : X n → ℝ) : ℝ :=
  ⨆ x : X n, ‖f x‖

/-- The γ-Hölder seminorm u_{C^{0,γ}} of a function -/
noncomputable def holderSeminorm (n : ℕ)
  (γ : ℝ≥0) (f : X n → ℝ) : ℝ :=
  ⨆ x: X n, ⨆ y : X n, ⨆ (h : x ≠ y), (‖f (x) - f (y)‖) / (rpow ‖x - y‖ γ)

/-- The complete γ-Hölder norm ‖u‖_{C^{0,γ}} combining C⁰ norm and Hölder seminorm -/
noncomputable def holderNorm (n : ℕ)
  (γ : ℝ≥0) (f : X n → ℝ) : ℝ :=
  normC0 n f + holderSeminorm n γ f

/-- The Hölder space C^{k,γ}(U) consists of k-times continuously differentiable functions
    whose k-th derivatives are Hölder continuous with exponent γ -/
structure Space (n k : ℕ) (C γ : ℝ≥0) :=
(to_fun : X n → ℝ)
(diff_k : ContDiff ℝ k to_fun)  -- k-times continuously differentiable
(holder_k : ∀ (α : ℕ) (hα : α ≤ k), HolderWith n C γ (deriv^[α] to_fun))  -- all derivatives up to k are Hölder continuous

/-- The norm on the Hölder space -/
noncomputable def spaceNorm (n k : ℕ) (C γ : ℝ≥0) (f : ) : ℝ :=
  ∑ α in Finset.range (k + 1), normC0 n (deriv^[α] f.to_fun) + holderSeminorm n γ (ContDiff ℝ α f.to_fun)

/-- By following properties from mathlib:
- HolderWith.continuous : Hölder continuous functions are continuous
- HolderWith.uniformContinuous : Hölder continuous functions are uniformly continuous
- holderWith_one : equivalence with Lipschitz continuity when γ = 1

We can prove that C^{k,γ} is a Banach space (left as sorry for now) -/
instance holderSpace.banachSpace (n k : ℕ) (C γ : ℝ≥0) :
  CompleteSpace (Space n k C γ) := sorry

end HolderSpace

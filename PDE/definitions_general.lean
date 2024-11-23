import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
--variable {n : Type*} [Fintype n] [DecidableEq n]
variable {n : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option diagnostics true
set_option diagnostics.threshold 30000

/-- Euclidean space of dimension n -/
abbrev Euc 𝕜 n := EuclideanSpace 𝕜 (Fin n)

/-- The standard basis vector in direction i for n-dimensional space. -/
def standardBasis (i : Fin n) : Euc 𝕜 n := fun j => if i = j then 1 else 0

/-- Any vector in Euclidean space is a sum of its basis components -/
theorem euc_eq_sum_basis (b : Euc 𝕜 n) : b = ∑ i, b i • standardBasis i := by {
  ext i
  unfold standardBasis
  rw [Finset.sum_apply]
  simp
}

/-- Partial derivative of a function f at point x in direction i.
    Defined as the line derivative with respect to the standard basis vector eᵢ. -/
noncomputable def partialDeriv (i : Fin n) (f : Euc 𝕜 n → F) (x : Euc 𝕜 n) : F :=
  lineDeriv 𝕜 f x (standardBasis i)

/-- A function has a partial derivative at x in direction i if it has a line derivative
    in the direction of the i-th standard basis vector. -/
def HasPartialDerivAt (i : Fin n) (f : Euc 𝕜 n → F) (f' : F) (x : Euc 𝕜 n) : Prop :=
  HasLineDerivAt 𝕜 f f' x (standardBasis i)

/-- A function is partially differentiable at x in direction i if it has a line derivative
    in the direction of the i-th standard basis vector. -/
def PartialDifferentiableAt (i : Fin n) (f : Euc 𝕜 n → F) (x : Euc 𝕜 n) : Prop :=
  LineDifferentiableAt 𝕜 f x (standardBasis i)

/-- Basic lemmas about partial derivatives -/
theorem partialDeriv_eq_of_hasPartialDerivAt
  {f : Euc 𝕜 n → F} {f' : F} {i : Fin n} {x : Euc 𝕜 n}
  (h : HasPartialDerivAt i f f' x) :
  partialDeriv i f x = f' :=
HasLineDerivAt.lineDeriv h

/-- Partial differentiability implies existence of partial derivative -/
theorem partialDifferentiableAt_iff_exists_partialDeriv
  {f : Euc 𝕜 n → F} {i : Fin n} {x : Euc 𝕜 n} :
  PartialDifferentiableAt i f x ↔ ∃ f', HasPartialDerivAt i f f' x :=
⟨fun h => ⟨partialDeriv i f x, LineDifferentiableAt.hasLineDerivAt h⟩,
 fun ⟨f', h⟩ => HasLineDerivAt.lineDifferentiableAt h⟩

/-- Uniqueness of partial derivatives when they exist -/
theorem hasPartialDerivAt.unique
  {f : Euc 𝕜 n → F} {f₁' f₂' : F} {i : Fin n} {x : Euc 𝕜 n}
  (h₁ : HasPartialDerivAt i f f₁' x)
  (h₂ : HasPartialDerivAt i f f₂' x) :
  f₁' = f₂' :=
HasLineDerivAt.unique h₁ h₂

/-
Looking at the original LineDeriv file, we see:

def lineDeriv (f : E → F) (x : E) (v : E) : F :=
  deriv (fun t ↦ f (x + t • v)) (0 : 𝕜)

def LineDifferentiableAt (f : E → F) (x : E) (v : E) : Prop :=
  DifferentiableAt 𝕜 (fun t ↦ f (x + t • v)) (0 : 𝕜)
-/

theorem lineDifferentiableAt_of_differentiableAt {f : E → F} {x : E}
  (hf : DifferentiableAt 𝕜 f x) (v : E) :
  LineDifferentiableAt 𝕜 f x v := by
  have hf_deriv := DifferentiableAt.hasFDerivAt hf
  have hf_lineDeriv := HasFDerivAt.hasLineDerivAt hf_deriv v
  exact HasLineDerivAt.lineDifferentiableAt hf_lineDeriv

theorem partialDifferentiableAt_of_differentiableAt {f : Euc 𝕜 n → F} {i : Fin n} {x : Euc 𝕜 n}
  (hf : DifferentiableAt 𝕜 f x) :
  PartialDifferentiableAt i f x :=
  lineDifferentiableAt_of_differentiableAt hf (standardBasis i)

/-- Line derivative of a sum is the sum of line derivatives -/
theorem lineDeriv_add (f g : E → F) (x v : E)
  (hf : LineDifferentiableAt 𝕜 f x v) (hg : LineDifferentiableAt 𝕜 g x v) :
  lineDeriv 𝕜 (fun y => f y + g y) x v = lineDeriv 𝕜 f x v + lineDeriv 𝕜 g x v := by
  -- Unfold definition to deriv
  simp only [lineDeriv]
  -- Get HasDerivAt from DifferentiableAt
  have hf_deriv := DifferentiableAt.hasDerivAt hf
  have hg_deriv := DifferentiableAt.hasDerivAt hg
  -- Their sum has a derivative
  have sum_deriv := HasDerivAt.add hf_deriv hg_deriv
  -- And it equals the sum of derivatives
  exact HasDerivAt.deriv sum_deriv

/-- Other basic properties follow similarly -/
theorem lineDeriv_sub (f g : E → F) (x v : E)
  (hf : LineDifferentiableAt 𝕜 f x v) (hg : LineDifferentiableAt 𝕜 g x v) :
  lineDeriv 𝕜 (fun y => f y - g y) x v = lineDeriv 𝕜 f x v - lineDeriv 𝕜 g x v := by
  simp only [lineDeriv]
  have hf_deriv := DifferentiableAt.hasDerivAt hf
  have hg_deriv := DifferentiableAt.hasDerivAt hg
  have sub_deriv := HasDerivAt.sub hf_deriv hg_deriv
  exact HasDerivAt.deriv sub_deriv

/-- Partial derivative of a sum is the sum of partial derivatives -/
theorem partialDeriv_add {i : Fin n} {f g : Euc 𝕜 n → F} {x : Euc 𝕜 n}
  (hf : LineDifferentiableAt 𝕜 f x (standardBasis i)) (hg : LineDifferentiableAt 𝕜 g x (standardBasis i)) :
  partialDeriv i (f + g) x = partialDeriv i f x + partialDeriv i g x := by
  -- Express partial derivative in terms of line derivatives
  simp only [partialDeriv]
  -- Use linearity of line derivatives
  have h := lineDeriv_add f g x (standardBasis i) (hf) (hg)
  -- The standardBasis is fixed, so this proves the result
  exact h

theorem lineDeriv_const_smul (f : E → F) (x v : E) (c : 𝕜) (hf : LineDifferentiableAt 𝕜 f x v) :
  lineDeriv 𝕜 (fun y => c • f y) x v = c • lineDeriv 𝕜 f x v := by
  have hf_deriv := DifferentiableAt.hasDerivAt hf
  have smul_deriv := HasDerivAt.smul (hasDerivAt_const 0 c) hf_deriv
  simp at smul_deriv
  exact HasDerivAt.deriv smul_deriv

/-- Partial derivative of scalar multiplication -/
theorem partialDeriv_smul {f : Euc 𝕜 n → F} {i : Fin n} {x : Euc 𝕜 n} (c : 𝕜)
    (hf : PartialDifferentiableAt i f x) :
    partialDeriv i (fun y => c • f y) x = c • partialDeriv i f x := by
  -- Express partial derivative in terms of line derivatives
  simp only [partialDeriv]
  -- Use linearity of line derivatives
  apply lineDeriv_const_smul
  exact hf

/-- Partial derivative of negation -/
theorem partialDeriv_neg {f : Euc 𝕜 n → F} {i : Fin n} {x : Euc 𝕜 n}
    (hf : PartialDifferentiableAt i f x) :
    partialDeriv i (fun y => -f y) x = -partialDeriv i f x := by
  -- Use the fact that - = (-1) •
  have h := partialDeriv_smul (-1 : 𝕜) hf
  simp [neg_one_smul] at h
  exact h

theorem lineDeriv_const (x v : E) (c : F) :
  lineDeriv 𝕜 (fun _ => c) x v = 0 := by
  -- The line derivative of a constant function is zero
  simp only [lineDeriv, hasDerivAt_const, deriv_const]

/-- Partial derivative of constant function -/
theorem partialDeriv_const {i : Fin n} {x : Euc 𝕜 n} (c : F) :
    partialDeriv i (fun _ => c) x = 0 := by
  -- Unfold to line derivative
  simp only [partialDeriv]
  -- Use the fact that line derivative of constant is zero
  exact lineDeriv_const x (standardBasis i) c


theorem partialDeriv_eq_fderiv {f : Euc 𝕜 n → F} (i : Fin n) (x : Euc 𝕜 n) (hf : DifferentiableAt 𝕜 f x) :
  partialDeriv i f x = fderiv 𝕜 f x (standardBasis i) :=
  DifferentiableAt.lineDeriv_eq_fderiv hf

/-- Partial derivative of composition -/
theorem partialDeriv_comp {i : Fin n} {f : Euc 𝕜 n → Euc 𝕜 m} {g : Euc 𝕜 m → F} {x : Euc 𝕜 n}
    (hf : PartialDifferentiableAt i f x) (hg : DifferentiableAt 𝕜 g (f x)) :
    partialDeriv i (g ∘ f) x = (fderiv 𝕜 g (f x)) (partialDeriv i f x) := by
  unfold partialDeriv lineDeriv
  unfold PartialDifferentiableAt at hf
  unfold LineDifferentiableAt at hf
  rw [←fderiv_deriv, ←fderiv_deriv]
  rw [show f x = f (x + (0:𝕜) • standardBasis i) from by simp] at hg
  have hcomp := fderiv_comp 0 hg hf
  rw [show (g ∘ fun t => f (x + t • standardBasis i)) = fun t => (g ∘ f) (x + t • standardBasis i) from by {
    ext s
    simp
  }] at hcomp
  rw [hcomp]
  simp

/-- Projection onto the i-th coordinate -/
def euc_proj (n : ℕ) (i : Fin n) : Euc 𝕜 n →L[𝕜] 𝕜 := ContinuousLinearMap.proj i

/-- Fderiv of projection is projection -/
theorem fderiv_euc_proj (i : Fin n) (x : Euc 𝕜 n) :
  fderiv 𝕜 (euc_proj n i) x = euc_proj n i := by
  simp [euc_proj]

/-- Coords of partial derivative is partial derivate of coords -/
theorem partialDeriv_coord {i : Fin n} {j : Fin m} {f : Euc 𝕜 n → Euc 𝕜 m} {x : Euc 𝕜 n}
  (hf : PartialDifferentiableAt i f x) :
  (partialDeriv i f x) j = partialDeriv i (fun y => f y j) x := by
  have hproj := ContinuousLinearMap.differentiableAt (euc_proj m j) (x := f x)
  have hcomp := partialDeriv_comp hf hproj
  rw [fderiv_euc_proj j (f x)] at hcomp
  simp [euc_proj, ContinuousLinearMap.proj, LinearMap.proj] at hcomp
  rw [←hcomp]
  congr


/-!
# Differential Operators

This file defines the fundamental differential operators of vector calculus:
* gradient (∇f)
* divergence (∇·F)
* curl (∇×F)
* laplacian (Δf = ∇·∇f)
-/

/-- Gradient of a scalar function f: ℝⁿ → ℝ.
    ∇f = (∂f/∂x₁, ..., ∂f/∂xₙ) -/
noncomputable def gradient (f : Euc 𝕜 n → 𝕜)
    (x : Euc 𝕜 n) : Euc 𝕜 n :=
  fun i => partialDeriv i f x

/-- Divergence of a vector field F: ℝⁿ → ℝⁿ.
    ∇·F = ∑ᵢ ∂Fᵢ/∂xᵢ -/
noncomputable def divergence (F : Euc 𝕜 n → Euc 𝕜 n)
    (x : Euc 𝕜 n) : 𝕜 :=
  ∑ i : Fin n, (partialDeriv i F x) i

/-- Cross product in ℝ³.
    a × b = (a₂b₃-a₃b₂, a₃b₁-a₁b₃, a₁b₂-a₂b₁) -/
noncomputable def cross_product (a b : Euc 𝕜 3) : Euc 𝕜 3 :=
  fun i => match i with
  | ⟨0, _⟩ => a 1 * b 2 - a 2 * b 1
  | ⟨1, _⟩ => a 2 * b 0 - a 0 * b 2
  | ⟨2, _⟩ => a 0 * b 1 - a 1 * b 0

/-- Curl of a vector field F: ℝ³ → ℝ³.
    ∇×F = (∂F₃/∂y - ∂F₂/∂z, ∂F₁/∂z - ∂F₃/∂x, ∂F₂/∂x - ∂F₁/∂y) -/
noncomputable def curl (F : Euc 𝕜 3 → Euc 𝕜 3)
    (x : Euc 𝕜 3) : Euc 𝕜 3 :=
  fun i => match i with
  | ⟨0, _⟩ => partialDeriv 1 (fun y => F y 2) x - partialDeriv 2 (fun y => F y 1) x
  | ⟨1, _⟩ => partialDeriv 2 (fun y => F y 0) x - partialDeriv 0 (fun y => F y 2) x
  | ⟨2, _⟩ => partialDeriv 0 (fun y => F y 1) x - partialDeriv 1 (fun y => F y 0) x

/-- Laplacian operator in n dimensions -/
noncomputable def laplacian (f : Euc 𝕜 n → 𝕜)
    (x : Euc 𝕜 n) : 𝕜 :=
  ∑ i : Fin n, partialDeriv i (fun y => partialDeriv i f y) x

/-- Alternative definition of Laplacian using divergence of gradient.
Δf = ∇·∇f -/
noncomputable def laplacian_alt (f : Euc 𝕜 n → 𝕜)
    (x : Euc 𝕜 n) : 𝕜 :=
  divergence (gradient f) x

-- Define a class for linear differential operators
-- TODO
-- class LinearDifferentialOperator
--   {𝕜 : Type _} [NontriviallyNormedField 𝕜]
--   {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
--   {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
--   {G : Type _} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
--   (L : (E → F) → (E → G)) where
--   toFun : (E → F) → (E → G) := L
--   --linearAt {f g : E → F} (x): IsLinearMap 𝕜 L-- or appropriate derivative condition

-- noncomputable instance : LinearDifferentialOperator (E:=Euc 𝕜 n) (F:=𝕜) (G:=Euc 𝕜 n) gradient where
--   toFun := gradient
--   linearAt := sorry

/-!
# Proofs of Vector Calculus Identities
-/

/-- Gradient of sum is sum of gradients -/
theorem gradient_sum (f g : Euc 𝕜 n → 𝕜) (x : Euc 𝕜 n) (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
  gradient (f + g) x = gradient f x + gradient g x := by
  -- Unfold gradient definition
  unfold gradient
  -- Extensionality: enough to prove equality at each component i
  ext i
  -- Use linearity of partial derivatives
  have hf_linederiv := lineDifferentiableAt_of_differentiableAt hf (standardBasis i)
  have hg_linederiv := lineDifferentiableAt_of_differentiableAt hg (standardBasis i)
  exact partialDeriv_add hf_linederiv hg_linederiv


/-- fderiv is inner product with gradient -/
theorem fderiv_eq_gradient_inner {f : Euc ℝ n → ℝ} {x b : Euc ℝ n} (hf : DifferentiableAt ℝ f x) :
  fderiv ℝ f x b = inner b (gradient f x) := by
  unfold gradient
  simp
  rw [euc_eq_sum_basis b]
  rw [map_sum]
  congr
  ext i
  rw [partialDeriv_eq_fderiv i x hf]
  simp
  rw [Finset.sum_apply]
  simp
  left
  unfold standardBasis
  simp

/-- Chain rule for gradient -/
theorem gradient_comp {f : Euc ℝ n → Euc ℝ m} {g : Euc ℝ m → ℝ} {x : Euc ℝ n}
  (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x)) :
  gradient (g ∘ f) x = fun i => inner (fderiv ℝ f x (standardBasis i)) (gradient g (f x)) := by
  ext i
  simp only [gradient]
  rw [partialDeriv_comp]
  rw [← fderiv_eq_gradient_inner hg]
  rw [partialDeriv_eq_fderiv i x hf]
  exact partialDifferentiableAt_of_differentiableAt hf
  exact hg

/-- Inner product of gradient chain rule -/
theorem inner_gradient_comp {f : Euc ℝ n → Euc ℝ m} {g : Euc ℝ m → ℝ} {x b : Euc ℝ n}
  (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x)) :
  (inner b (gradient (g ∘ f) x) : ℝ) = inner (fderiv ℝ f x b) (gradient g (f x)) := by
  rw [← fderiv_eq_gradient_inner]
  rw [← fderiv_eq_gradient_inner]
  rw [fderiv_comp]
  simp
  assumption; assumption; assumption
  exact DifferentiableAt.comp x hg hf

/-- Divergence of sum is sum of divergences -/
theorem divergence_sum (F G : Euc 𝕜 n → Euc 𝕜 n) (x : Euc 𝕜 n) (hf : DifferentiableAt 𝕜 F x) (hg : DifferentiableAt 𝕜 G x) :
  divergence (F + G) x = divergence F x + divergence G x := by
  -- Unfold divergence definition
  unfold divergence
  -- Distribute sum over addition
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  -- Use linearity of partial derivatives
  intro i _
  have hf_linederiv := lineDifferentiableAt_of_differentiableAt hf (standardBasis i)
  have hg_linederiv := lineDifferentiableAt_of_differentiableAt hg (standardBasis i)
  rw [←Pi.add_apply]
  rw [partialDeriv_add hf_linederiv hg_linederiv]

/-- Curl of sum is sum of curls -/
theorem curl_sum
    (F G : Euc 𝕜 3 → Euc 𝕜 3)
    (x : Euc 𝕜 3) (hf : DifferentiableAt 𝕜 F x) (hg : DifferentiableAt 𝕜 G x) :
  curl (F + G) x = curl F x + curl G x := by
  sorry
  -- -- Unfold curl definition
  -- simp only [curl]
  -- -- Extensionality: enough to prove equality for each component
  -- ext i
  -- -- Case analysis on components
  -- match i with
  -- | ⟨0, _⟩ =>
  --   -- Use linearity of partial derivatives and subtraction
  --   simp [partialDeriv_add]
  --   ring
  -- | ⟨1, _⟩ =>
  --   simp [partialDeriv_add]
  --   ring
  -- | ⟨2, _⟩ =>
  --   simp [partialDeriv_add]
  --   ring

/-- The two definitions of Laplacian are equivalent -/
theorem laplacian_eq_laplacian_alt (f : Euc 𝕜 n → 𝕜) (x : Euc 𝕜 n) :
  laplacian f x = laplacian_alt f x := by
  -- Unfold both definitions
  simp only [laplacian, laplacian_alt, divergence, gradient]
  unfold gradient
  -- Both are sums over second derivatives
  apply Finset.sum_congr rfl
  intro j _
  -- Show equality of second derivatives

  apply partialDeriv_eq_of_hasPartialDerivAt
  -- Would need to show second derivatives commute
  sorry

/-- Curl of gradient is zero -/
theorem curl_gradient (f : EuclideanSpace ℝ (Fin 3) → ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
  curl (gradient f) x = 0 := by
  -- Unfold definitions
  simp only [curl, gradient]
  -- Extensionality
  ext i
  -- Case analysis on components
  match i with
  | ⟨0, _⟩ =>
    -- Show ∂²f/∂y∂z = ∂²f/∂z∂y using commutativity of mixed partials
    sorry
  | ⟨1, _⟩ =>
    -- Show ∂²f/∂z∂x = ∂²f/∂x∂z
    sorry
  | ⟨2, _⟩ =>
    -- Show ∂²f/∂x∂y = ∂²f/∂y∂x
    sorry

/-- Divergence of curl is zero -/
theorem divergence_curl
    (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 3)) :
  divergence (curl F) x = 0 := by
  -- Unfold definitions
  simp only [divergence, curl]
  -- Rearrange terms using commutativity of mixed partials
  sorry
  -- Would need to show that the sum of terms cancels out
  -- Each term appears twice with opposite signs due to cyclic property



/- -- MAIN FILE For PDEs -- !-/
/-- Multi-index for denoting partial derivatives -/
structure MultiIndex (n : ℕ) where
  index : Fin n → ℕ

/-- Order of a multi-index: sum of all components -/
def MultiIndex.order {n : ℕ} (α : MultiIndex n) : ℕ :=
  Finset.sum (Finset.univ : Finset (Fin n)) (fun i => α.index i)

/-- |α| ≤ k predicate for multi-indices -/
def MultiIndex.leq {n : ℕ} (α : MultiIndex n) (k : ℕ) : Prop :=
  α.order ≤ k

/-- |α| = k predicate for multi-indices -/
def MultiIndex.eq {n : ℕ} (α : MultiIndex n) (k : ℕ) : Prop :=
  α.order = k

/-- General k-th order partial differential equation.
    F(D^k u(x), D^{k-1} u(x), ..., Du(x), u(x), x) = 0 -/
structure GeneralPDE (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (n k : ℕ) where
  /-- The equation operator -/
  eqn : (E → F) → E → F
  /-- The domain where the equation holds -/
  domain : Set E := Set.univ
  /-- The order of highest derivatives that appear -/
  order : ℕ := k

/-- Linear PDE: Σ aₐ(x)D^α u = f(x) -/
structure LinearPDE (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (n k : ℕ) extends GeneralPDE 𝕜 E F n k where
  /-- Coefficients aₐ(x) for each multi-index α -/
  coeffs : Π (α : MultiIndex n), α.leq k → (E → F)
  /-- Right-hand side function f(x) -/
  rhs : E → F
  /-- The equation has the form Σ aₐ(x)D^α u = f(x) -/
  is_linear : True  -- This is a type class marker

/-- Homogeneous Linear PDE: special case where f ≡ 0 -/
def LinearPDE.isHomogeneous {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {n k : ℕ} (pde : LinearPDE 𝕜 E F n k) : Prop :=
  ∀ x, pde.rhs x = 0

/-- Semilinear PDE: Σ aₐ(x)D^α u + a₀(D^{k-1}u,...,Du,u,x) = 0 -/
structure SemilinearPDE (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (n k : ℕ) extends GeneralPDE 𝕜 E F n k where
  /-- Coefficients aₐ(x) for highest order terms -/
  coeffs : Π (α : MultiIndex n), α.eq k → (E → F)
  /-- Lower order nonlinear term -/
  nonlinear_term : (E → F) → E → F
  /-- The equation has semilinear form -/
  is_semilinear : True

/-- Quasilinear PDE: Σ aₐ(D^{k-1}u,...,Du,u,x)D^α u + a₀(D^{k-1}u,...,Du,u,x) = 0 -/
structure QuasilinearPDE (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (n k : ℕ) extends GeneralPDE 𝕜 E F n k where
  /-- Coefficients aₐ that depend on lower order derivatives -/
  coeffs : Π (α : MultiIndex n), α.eq k → ((E → F) → E → F)
  /-- Lower order nonlinear term -/
  nonlinear_term : (E → F) → E → F
  /-- The equation has quasilinear form -/
  is_quasilinear : True

/-- Fully Nonlinear PDE: F depends nonlinearly on highest order derivatives -/
structure FullyNonlinearPDE (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (n k : ℕ) extends GeneralPDE 𝕜 E F n k where
  /-- The equation is truly nonlinear in highest derivatives -/
  is_fully_nonlinear : True

/-- System of PDEs: multiple equations for multiple unknown functions -/
structure PDESystem (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (n k m : ℕ) where
  /-- System of m equations F₁ = 0, ..., Fₘ = 0 -/
  eqns : Fin m → (E → F) → E → F
  /-- Domain where the system holds -/
  domain : Set E := Set.univ
  /-- Order of the system -/
  order : ℕ := k

/-!
# Examples of PDEs

This file contains concrete examples of common PDEs using our framework.
We work over the real numbers and use built-in Rⁿ.
-/

noncomputable def laplace_equation (n : ℕ) : LinearPDE ℝ (EuclideanSpace ℝ (Fin n)) ℝ n 2 where
  eqn := fun u x => laplacian u x
  coeffs := fun α h =>
    if α.order = 2 then fun _ => (1 : ℝ) else fun _ => (0 : ℝ)
  rhs := fun _ => (0 : ℝ)
  is_linear := trivial
  domain := Set.univ

/-- Heat equation: uₜ - Δu = 0
    Here we work in 2 dimensions, where the first coordinate is time -/
noncomputable def heat_equation (n : ℕ) : LinearPDE ℝ (EuclideanSpace ℝ (Fin 2)) ℝ 2 1 where
  eqn := fun u x =>
    partialDeriv u 0 x - laplacian (fun y => u y) x
  coeffs := fun α h =>
    if α.order = 1 && α.index 0 = 1 then fun _ => (1 : ℝ)
    else if α.order = 2 then fun _ => (-1 : ℝ)
    else fun _ => (0 : ℝ)
  rhs := fun _ => (0 : ℝ)
  is_linear := trivial
  domain := Set.univ

/-- Inviscid Burgers' equation: uₜ + uuₓ = 0 -/
noncomputable def burgers_equation : FullyNonlinearPDE ℝ (EuclideanSpace ℝ (Fin 2)) ℝ 2 1 where
  eqn := fun u x =>
    partialDeriv u 0 x + (u x) * (partialDeriv u 1 x)
  domain := Set.univ
  is_fully_nonlinear := trivial

/-- KdV equation: uₜ + uuₓ + uₓₓₓ = 0 -/
noncomputable def kdv_equation : FullyNonlinearPDE ℝ (EuclideanSpace ℝ (Fin 2)) ℝ 2 3 where
  eqn := fun u x =>
    partialDeriv u 0 x +
    (u x) * (partialDeriv u 1 x) +
    partialDeriv (fun y => partialDeriv (fun z => partialDeriv u 1 z) 1 y) 1 x
  domain := Set.univ
  is_fully_nonlinear := trivial

/-!
# Transport Equation with Initial Value Problem

This file formalizes the transport equation and its initial value problem:
uₜ + b·∇u = 0 in ℝⁿ × (0,∞)
u = g   on ℝⁿ × {t=0}

where b = (b₁,...,bₙ) is a fixed vector in ℝⁿ.
-/

/-- The transport equation domain: ℝⁿ × (0,∞) -/
def TransportDomain (n : ℕ) : Set (Euc ℝ (n+1)) :=
  {x | 0 < x 0}  -- x₀ represents time t

/-- Initial data domain: ℝⁿ × {t=0} -/
def InitialDomain (n : ℕ) : Set (Euc ℝ (n+1)) :=
  {x | x 0 = 0}  -- x₀ represents time t

/-- Projection onto the time coordinate -/
noncomputable def timeCoord (n : ℕ) : Euc ℝ (n+1) →L[ℝ] ℝ := euc_proj (n+1) 0

/-- Time coordinate is first coordinate -/
@[simp]
theorem timeCoord_is_first (n : ℕ) : timeCoord n = euc_proj (n+1) 0 := rfl

/-- Projection onto the spatial coordinates -/
noncomputable def spatialCoord (n : ℕ) : Euc ℝ (n+1) →L[ℝ] Euc ℝ n := {
  toFun := fun x => fun i => x (i + 1),
  map_add' := fun x y => funext (fun i => by simp),
  map_smul' := fun c x => funext (fun i => by simp),
  cont := by
    apply continuous_pi
    intro i
    simp
    apply continuous_apply (i + 1 : Fin (n+1))
}

/-- Spatial coordinate at index i -/
@[simp]
theorem spatialCoord_apply (n : ℕ) (i : Fin n) (x : Euc ℝ (n+1)) : spatialCoord n x i = x (i + 1) := rfl

/-- Embedding of ℝⁿ into ℝⁿ⁺¹, with time coordinate 0 -/
noncomputable def embed_with_time_zero (n : ℕ) : Euc ℝ n →L[ℝ] Euc ℝ (n+1) := {
  toFun := fun x => fun i =>
    if h : i = 0 then 0 else x (i.pred h),
  map_add' := fun x y => funext (fun i => by {
    by_cases h : i = 0
    · simp [h]
    · simp [h]
  }),
  map_smul' := fun c x => funext (fun i => by simp),
  cont := by
    apply continuous_pi
    intro i
    simp
    by_cases h : i = 0
    · simp [h]
      apply continuous_const
    · simp [h]
      apply continuous_apply (i.pred h)
}

/-- Spatial gradient of a function (excluding time derivative) -/
noncomputable def spatial_gradient {n : ℕ} (u : Euc ℝ (n+1) → ℝ)
    (x : Euc ℝ (n+1)) : Euc ℝ n := spatialCoord n (gradient u x)

/-- The type of operators in a PDE -/
abbrev PDEOperator (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G] := (E → F) → E → G

/-- A PDE equation of the form Pf(x) = g(x) -/
structure PDEEquation (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] where
  /-- The output type -/
  output : Type*
  [output_normed_add_comm_group : NormedAddCommGroup output]
  [output_normed_space : NormedSpace 𝕜 output]
  /-- The operator -/
  operator : PDEOperator 𝕜 E F output
  /-- The right-hand side -/
  rhs : E → output
  /-- The domain -/
  domain : Set E

/-- A PDE problem is -/
structure PDEProblem (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] where
  /-- The equations -/
  eqns : List (PDEEquation 𝕜 E F)
  /-- Initial conditions -/
  initial_conditions : List (PDEEquation 𝕜 E F)

/-- Satisfies a PDE problem -/
def IsSolutionPDEProblem (pde : PDEProblem 𝕜 E F) (u : E → F) : Prop :=
  ∀ eqn ∈ pde.eqns ++ pde.initial_conditions, ∀ x ∈ eqn.domain, eqn.operator u x = eqn.rhs x

/-- Initial value problem for transport equation -/
noncomputable def transportIVP {n : ℕ} (b : Euc ℝ n) (g : Euc ℝ n → ℝ) (hg : ∀ x, DifferentiableAt ℝ g x) : PDEProblem ℝ (Euc ℝ (n+1)) ℝ where
  eqns := [{
    output := ℝ
    operator := fun u x =>
      partialDeriv 0 u x + inner (spatial_gradient u x) b
    rhs := fun _ => 0
    domain := TransportDomain n
  }]
  initial_conditions := [{
    output := ℝ
    operator := id
    rhs := g ∘ spatialCoord n
    domain := InitialDomain n
  }]

/-- The method of characteristics solution: u(x,t) = g(x - tb) -/
noncomputable def transportSolution {n : ℕ} (b : Euc ℝ n) (g : Euc ℝ n → ℝ) :
    Euc ℝ (n+1) → ℝ :=
fun x => g (fun i => x (i + 1) - (x 0) * b i)

/-- TransportSolution is a solution to the transport IVP -/
theorem transportSolution_is_solution {n : ℕ} (b : Euc ℝ n) (g : Euc ℝ n → ℝ) (hg : ∀ x, DifferentiableAt ℝ g x) :
  IsSolutionPDEProblem (transportIVP b g hg) (transportSolution b g) := by {
  -- Unfold what it means to be a solution
  unfold IsSolutionPDEProblem
  -- Split into main equation and initial condition
  intro eqn heqn x hx
  simp at heqn
  rcases heqn with (hpde | hinitial)

  -- Case 1: The PDE equation
    -- Simplify to show we have the transport equation
  · simp [transportIVP] at hpde
    -- Now have one equation, substitute it
    subst hpde
    -- This gives us the actual transport equation to prove
    unfold transportSolution

    -- Similar to original proof from here
    let transport_linear_map : Euc ℝ (n+1) →L[ℝ] Euc ℝ n :=
      spatialCoord n - (ContinuousLinearMap.smulRight (timeCoord n) b)

    have hglinear : transportSolution b g = g ∘ transport_linear_map := by {
      ext1 x
      simp [transportSolution, transport_linear_map]
      congr
    }
    have htime : partialDeriv 0 (transportSolution b g)
      = fun x => -inner b (gradient g (transport_linear_map x)) := by {
      ext1 x
      rw [hglinear]
      rw [partialDeriv_comp]
      · rw [fderiv_eq_gradient_inner]
        · have hdtTLM : partialDeriv 0 (transport_linear_map) x = -b := by {
            rw [partialDeriv_eq_fderiv 0]
            · rw [ContinuousLinearMap.fderiv]
              ext i
              simp [transport_linear_map, standardBasis]
              simp [(Fin.succ_ne_zero i).symm]
              simp [euc_proj, ContinuousLinearMap.proj, LinearMap.proj, standardBasis]
            · exact ContinuousLinearMap.differentiableAt transport_linear_map
          }
          rw [hdtTLM]
          simp
        · apply hg
      · apply partialDifferentiableAt_of_differentiableAt
        exact ContinuousLinearMap.differentiableAt transport_linear_map
      apply hg
    }

    have hspatial : spatial_gradient (transportSolution b g) = fun x =>
      gradient g (transport_linear_map x) := by {
      ext1 x
      -- Proof that spatial gradient matches
      unfold spatial_gradient
      rw [hglinear]
      rw [gradient_comp]
      rw [ContinuousLinearMap.fderiv]
      set v := gradient g (transport_linear_map x)
      ext i
      simp [transport_linear_map, standardBasis]
      conv => {
        lhs; enter [2, j]
        rw [sub_mul]
        simp
        simp [euc_proj, ContinuousLinearMap.proj, LinearMap.proj, standardBasis]
        simp [Fin.succ_ne_zero i]
      }
      simp
      exact ContinuousLinearMap.differentiableAt transport_linear_map
      apply hg
    }

    -- Combine the parts
    simp
    have htransportSln : transportSolution b g = fun x => g fun i => x (i + 1) - x 0 * b i := by {
      ext y
      simp [transportSolution]
    }
    rw [← htransportSln]
    simp [htime, hspatial]
    conv => {
      lhs; enter [1,1,2,j]
      rw [mul_comm]
    }
    simp

  -- Case 2: The initial condition
    -- Simplify to show we have the initial condition
  · simp [transportIVP] at hinitial
    -- Now have one equation, substitute it
    subst hinitial
    -- Need to show that at t=0, solution matches initial data
    simp [transportSolution]
    have h0 : x 0 = 0 := by {
      -- Use the domain condition
      simp [InitialDomain] at hx
      exact hx
    }
    -- When t=0, x - tb = x, so we get g(x) as required
    simp [h0, spatialCoord]
}


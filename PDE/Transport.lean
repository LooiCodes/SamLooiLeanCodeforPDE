import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Asymptotics.Asymptotics
import PDE.Definitions

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
--variable {n : Type*} [Fintype n] [DecidableEq n]
variable {n m : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option diagnostics true
set_option diagnostics.threshold 30000


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
noncomputable def transportFunction {n : ℕ} (b : Euc ℝ n) (g : Euc ℝ n → ℝ) :
    Euc ℝ (n+1) → ℝ :=
fun x => g (fun i => x (i + 1) - (x 0) * b i)

/-- TransportSolution is a solution to the transport IVP -/
theorem transportFunction_is_solution {n : ℕ} (b : Euc ℝ n) (g : Euc ℝ n → ℝ) (hg : ∀ x, DifferentiableAt ℝ g x) :
  IsSolutionPDEProblem (transportIVP b g hg) (transportFunction b g) := by {
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
    unfold transportFunction

    -- Similar to original proof from here
    let transport_linear_map : Euc ℝ (n+1) →L[ℝ] Euc ℝ n :=
      spatialCoord n - (ContinuousLinearMap.smulRight (timeCoord n) b)

    have hglinear : transportFunction b g = g ∘ transport_linear_map := by {
      ext1 x
      simp [transportFunction, transport_linear_map]
      congr
    }
    have htime : partialDeriv 0 (transportFunction b g)
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

    have hspatial : spatial_gradient (transportFunction b g) = fun x =>
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
    have htransportSln : transportFunction b g = fun x => g fun i => x (i + 1) - x 0 * b i := by {
      ext y
      simp [transportFunction]
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
    simp [transportFunction]
    have h0 : x 0 = 0 := by {
      -- Use the domain condition
      simp [InitialDomain] at hx
      exact hx
    }
    -- When t=0, x - tb = x, so we get g(x) as required
    simp [h0, spatialCoord]
}

#check Asymptotics.IsLittleO

theorem hasDerivAt_euc_iff_fin {φ : ℝ → Euc ℝ n} {φ' : Euc ℝ n} {x : ℝ} :
    HasDerivAt φ φ' x ↔ HasDerivAt (fun x i => φ x i) (fun i => φ' i) x := by
  unfold HasDerivAt HasDerivAtFilter
  simp only [hasFDerivAtFilter_iff_isLittleO]
  simp
  simp_rw [Asymptotics.isLittleO_pi]

  simp_rw [fderiv_pi_apply]
  simp
  convert Asymptotics.isLittleO_pi
  apply?
  simp only [ContinuousLinearMap.coe_pi]

/-- A solution to the transport IVP is transportFunction -/
theorem transport_solution_is_transportFunction {n : ℕ} (b : Euc ℝ n) (g : Euc ℝ n → ℝ)
    (hg : ∀ x, DifferentiableAt ℝ g x) (u : Euc ℝ (n+1) → ℝ)
    (hu : ∀ x, DifferentiableAt ℝ u x)
    (hsln : IsSolutionPDEProblem (transportIVP b g hg) u) :
    u = transportFunction b g := by {
  -- Step 1: Setup - show equality by showing they match at arbitrary point
  ext x

  -- Characteristic curve (for all t ≥ 0)
  -- γ(s) = (s, x + (s - t)b)
  let γ : ℝ → Euc ℝ (n+1) := fun s =>
    fun i => if h : i = 0 then s else x (i) + (s - x 0) * b (i.pred h)
  let b1 : Euc ℝ (n+1) := fun i => if h : i = 0 then 1 else b (i.pred h)
  let γlinear : ℝ →L[ℝ] Euc ℝ (n+1) :=
    ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) b1

  -- Derivative of γ(s) is (1, b)
  have hγhasDerivAt : ∀ s, HasDerivAt γ (fun i => if h : i = 0 then 1 else b (i.pred h)) s := by {
    intro s
    -- For each coordinate i, show the derivative exists
    ext i
    -- Case split on whether i = 0 (time coordinate) or not
    by_cases hi : i = 0
    · -- Case i = 0: time coordinate
      simp [γ, hi]
      -- The derivative is 1 since γ₀(s) = s
      exact hasDerivAt_id s
    · -- Case i ≠ 0: spatial coordinate
      simp [γ, hi]
      -- Square both sides
      rw [sq_eq_sq]
      -- The derivative is b_i since γᵢ(s) = xᵢ + (s-t)bᵢ
      -- Use linearity of derivative
      have h_deriv := hasDerivAt_const (x i)
      have h_mul := hasDerivAt_mul_const (s - x 0) (b (i.pred hi))
      exact hasDerivAt_add h_deriv h_mul
  }

  -- Define h(s) = u(γ(s))
  let h := fun s => u (γ s)

  -- Show h is differentiable (needs detailed proof)
  have hdiff : ∀ s, DifferentiableAt ℝ h s := by {
    sorry
  }

  -- Show h'(s) = 0 using PDE equation
  have hderiv : ∀ s, deriv h s = 0 := by {
    sorry
  }

  -- Apply fundamental theorem of calculus
  have hconst : ∀ x, h x = h 0 := by {
    sorry
  }

  have h0 : u x = h (x 0) := by {
    sorry
  }
  -- Show u(x) = u(γ(x₀)) = u(γ(0)) = g(spatialCoord n x - x₀b)
  -- which is exactly transportFunction b g x
  rw [h0, hconst]

  -- Initial condition
  have hinit : ∀ y : Euc ℝ n, u (embed_with_time_zero n y) = g y := by {
    sorry
  }
  simp [transportFunction, h, γ]
  convert hinit (spatialCoord n x - x 0 • b) with i
  by_cases h : i = 0
  · rw [h]
    simp
  · simp [h]
    congr
    let j := i.pred h
    have hj : i = j.succ := by simp [j]
    rw [hj]
    simp
}

theorem my_theorem {α β : Type*} [NormedAddCommGroup β] {l : Filter α}
    {f h g : α → β} (hfg : IsLittleO f g l) (hfh : IsTheta f h l) :
    IsLittleO h g l := by
  -- Use transitivity of little-o with big-Theta
  apply isLittleO_trans_isTheta
  · exact hfg
  · exact isTheta_symm hfh

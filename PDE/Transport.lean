import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
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

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
import Mathlib.Analysis.Calculus.MeanValue
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
  -- TODO: Change to (0,∞)
  {x | 0 ≤ x 0}  -- x₀ represents time t

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
      ext i
      simp
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
              simp [transport_linear_map]
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
      simp [transport_linear_map]
      simp
      exact hg (transport_linear_map x)
    }

    -- Combine the parts
    simp
    have htransportSln : transportFunction b g = fun x => g fun i => x (i.succ) - x 0 * b i := by {
      ext y
      simp [transportFunction]
    }
    rw [← htransportSln]
    simp [htime, hspatial]
    rw [AdjointSpace.real_inner_comm]
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

theorem transportIVP_eqns {n : ℕ} (b : Euc ℝ n) (g : Euc ℝ n → ℝ) (hg : ∀ x, DifferentiableAt ℝ g x) :
  (transportIVP b g hg).eqns = [{
    output := ℝ
    operator := fun u x => partialDeriv 0 u x + inner (spatial_gradient u x) b
    rhs := fun _ => 0
    domain := TransportDomain n
  }] := by {
  simp [transportIVP]
}

theorem isSolutionPDEProblem_transport_unfold {n : ℕ} {b : Euc ℝ n} {g : Euc ℝ n → ℝ}
    {hg : ∀ x, DifferentiableAt ℝ g x} {u : Euc ℝ (n+1) → ℝ}
    {hu : ∀ x, DifferentiableAt ℝ u x}
    (hsln : IsSolutionPDEProblem (transportIVP b g hg) u) :
    (∀ x ∈ TransportDomain n, partialDeriv 0 u x + inner (spatial_gradient u x) b = 0) ∧
    ∀ x ∈ InitialDomain n, u x = g ((spatialCoord n) x) := by {
  unfold IsSolutionPDEProblem at hsln
  simp at hsln
  simp [transportIVP] at hsln
  assumption
}

/-- A solution to the transport IVP is transportFunction -/
theorem transport_solution_is_transportFunction {n : ℕ} (b : Euc ℝ n) (g : Euc ℝ n → ℝ)
    (hg : ∀ x, DifferentiableAt ℝ g x) (u : Euc ℝ (n+1) → ℝ)
    (hu : ∀ x, DifferentiableAt ℝ u x)
    (hsln : IsSolutionPDEProblem (transportIVP b g hg) u) :
    ∀ x ∈ TransportDomain n, u x = transportFunction b g x := by {
  -- Step 1: Setup - show equality by showing they match at arbitrary point
  intro x hx

  -- Characteristic curve (for all t ≥ 0)
  -- γ(s) = (s, x + (s - t)b)
  set γ : ℝ → Euc ℝ (n+1) := fun s =>
    fun i => if h : i = 0 then s else x (i) + (s - x 0) * b (i.pred h) with hγ; clear_value γ
  set b1 : Euc ℝ (n+1) := fun i => if h : i = 0 then 1 else b (i.pred h) with hb1; clear_value b1
  let γlinear : ℝ →L[ℝ] Euc ℝ (n+1) :=
    ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) b1

  -- Derivative of γ(s) is (1, b)
  have hγhasDerivAt : ∀ s, HasDerivAt γ (fun i => if h : i = 0 then 1 else b (i.pred h)) s := by {
    intro s
    rw [hasDerivAt_pi]
    intro i
    simp [hγ]
    by_cases hi : i = 0
    · simp [hi]
      exact hasDerivAt_id s
    · simp [hi]
      conv => {
        enter [1,y]
        rw [sub_mul]
      }
      apply HasDerivAt.const_add
      apply HasDerivAt.add_const
      apply hasDerivAt_mul_const
  }

  have hγdiff : ∀ s, DifferentiableAt ℝ γ s := by {
    intro s
    exact HasFDerivAt.differentiableAt (hγhasDerivAt s)
  }

  -- Define f(s) = u(γ(s))
  set f := fun s => u (γ s) with hf; clear_value f

  -- Show f is differentiable
  have hfdiff : ∀ s, DifferentiableAt ℝ f s := by {
    rw [hf]
    intro s
    apply DifferentiableAt.comp
    apply hu
    apply hγdiff
  }

  have hpde1 : ∀ x ∈ TransportDomain n, partialDeriv 0 u x + inner (spatial_gradient u x) b = 0 := by {
    exact (isSolutionPDEProblem_transport_unfold (hu:=hu) hsln).left
  }
  have hpde2 : ∀ x ∈ InitialDomain n, u x = g ((spatialCoord n) x) := by {
    exact (isSolutionPDEProblem_transport_unfold (hu:=hu) hsln).right
  }
  clear hsln
  -- Show f'(s) = 0 using PDE equation
  have hfderiv : ∀ s ≥ 0, deriv f s = 0 := by {
    intro s hs
    rw [hf]
    rw [←fderiv_deriv]
    rw [show (fun t => u (γ t)) = u ∘ γ from by {
      ext t; simp
    }]
    rw [fderiv_comp s]
    simp
    rw [fderiv_eq_gradient_inner]
    rw [inner_split_time_space]
    rw [HasDerivAt.deriv (hγhasDerivAt s)]
    simp
    rw [←spatial_gradient]
    conv => {
      lhs; enter [2,1]
      rw [show (spatialCoord n) (fun i ↦ if h : i = 0 then 1 else b (i.pred h)) = b from by {
        ext i
        simp
        intro contra
        cases contra
      }]
    }
    rw [AdjointSpace.real_inner_comm]
    apply hpde1
    simp [TransportDomain, hγ]
    assumption

    -- Proving differentiability
    apply hu
    apply hu
    apply hγdiff
  }

  -- Apply fundamental theorem of calculus
  have hfconst : ∀ x ≥ 0, f x = f 0 := by {
    intro x hx
    apply Convex.is_const_of_fderivWithin_eq_zero (𝕜:=ℝ) (s:=Set.Ici 0)
    · exact convex_Ici 0
    · intro y hy
      exact DifferentiableAt.differentiableWithinAt (hfdiff y)
    · intro y hy
      rw [fderivWithin_eq_fderiv]
      exact ContinuousLinearMap.ext_ring (hfderiv y hy)
      exact (uniqueDiffOn_Ici 0).uniqueDiffWithinAt hy
      exact hfdiff y
    · exact hx
    · exact Set.left_mem_Ici
  }

  have h0 : u x = f (x 0) := by {
    rw [hf, hγ]
    congr
    simp
    ext i
    split_ifs with hi
    · rw [hi]
    · rfl
  }
  -- Show u(x) = u(γ(x₀)) = u(γ(0)) = g(spatialCoord n x - x₀b)
  -- which is exactly transportFunction b g x
  rw [h0, hfconst]

  -- Initial condition
  have hinit : ∀ y : Euc ℝ n, u (embed_with_time_zero n y) = g y := by {
    intro y
    set z := embed_with_time_zero n y with hz; clear_value z
    have hy : y = spatialCoord n z := by {
      rw [hz]
      simp
    }
    rw [hy]
    apply hpde2
    simp [InitialDomain]
    rw [hz]
    simp
  }
  simp [transportFunction, hf, hγ]
  convert hinit (spatialCoord n x - x 0 • b) with i i
  split_ifs with hi
  · rw [hi]
    simp
  · simp [hi]
    congr
    let j := i.pred hi
    have hj : i = j.succ := by simp [j]
    rw [hj]
    simp
  simp
  exact hx
}

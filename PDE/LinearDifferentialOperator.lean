import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.Real.Basic
import PDE.Definitions

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
--variable {n : Type*} [Fintype n] [DecidableEq n]
variable {n m : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]

class LinearDifferentialOperator (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] (operator : (E → F) → E → G) where
  linear_smul : ∀ (c : 𝕜) (f : E → F) (x : E) (_ : DifferentiableAt 𝕜 f x), operator (c • f) x = c • operator f x
  linear_add : ∀ (f g : E → F) (x : E) (_ : DifferentiableAt 𝕜 f x) (_ : DifferentiableAt 𝕜 g x), operator (f + g) x = operator f x + operator g x

namespace LinearDifferentialOperator

variable {op op1 op2 : (E → F) → E → G} [inst : LinearDifferentialOperator 𝕜 op] [LinearDifferentialOperator 𝕜 op1] [LinearDifferentialOperator 𝕜 op2]

theorem op_smul {c : 𝕜} {f : E → F} {x : E} {hf : DifferentiableAt 𝕜 f x} (op : (E → F) → E → G) [LinearDifferentialOperator 𝕜 op] :
  op (c • f) x = c • op f x := by
  apply linear_smul
  assumption

theorem op_add {f g : E → F} {x : E} {hf : DifferentiableAt 𝕜 f x} {hg : DifferentiableAt 𝕜 g x} (op : (E → F) → E → G) [inst : LinearDifferentialOperator 𝕜 op] :
  op (f + g) x = op f x + op g x := by
  apply inst.linear_add
  assumption
  assumption

theorem op_neg {f : E → F} {x : E} {hf : DifferentiableAt 𝕜 f x} (op : (E → F) → E → G) [inst : LinearDifferentialOperator 𝕜 op] :
  op (-f) x = -op f x := by
  have h : (-1 : 𝕜) • f = -f := by simp
  rw [←h, op_smul (op:=op)]
  simp
  assumption

theorem op_sub {f g : E → F} {x : E} {hf : DifferentiableAt 𝕜 f x} {hg : DifferentiableAt 𝕜 g x} (op : (E → F) → E → G) [inst : LinearDifferentialOperator 𝕜 op] :
  op (f - g) x = op f x - op g x := by
  simp [sub_eq_add_neg]
  rw [op_add (𝕜:=𝕜) op]
  rw [op_neg (𝕜:=𝕜) op]
  assumption; assumption
  apply DifferentiableAt.neg hg



----------------------------------------------------------------------------------------------------
-- Instances ---------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
instance instFderivLDO : LinearDifferentialOperator (𝕜:=𝕜) (E:=E) (F:=F) (G:=E →L[𝕜] F) (fun f x => fderiv 𝕜 f x) where
  linear_smul := by {
    intro c f x hf
    exact fderiv_const_smul' hf c
  }
  linear_add := by {
    intro f g x hf hg
    exact fderiv_add hf hg
  }

instance instDerivLDO : LinearDifferentialOperator (𝕜:=𝕜) (E:=𝕜) (F:=F) (G:=F) (fun f x => deriv f x) where
  linear_smul := by {
    intro c f x hf
    rw [←fderiv_deriv, ←fderiv_deriv]
    rw [show fderiv 𝕜 (c • f) x = c • fderiv 𝕜 f x from linear_smul c f x hf]
    simp
  }
  linear_add := by {
    intro f g x hf hg
    rw [←fderiv_deriv, ←fderiv_deriv]
    rw [show fderiv 𝕜 (f + g) x = fderiv 𝕜 f x + fderiv 𝕜 g x from linear_add f g x hf hg]
    simp
  }

  instance instLineDerivLDO (v : E) : LinearDifferentialOperator (𝕜:=𝕜) (E:=E) (F:=F) (G:=F) (fun f x => lineDeriv 𝕜 f x v) where
    linear_smul := by {
      intro c f x hf
      unfold lineDeriv
      simp
      exact deriv_const_smul' c
    }
    linear_add := by {
      intro f g x hf hg
      unfold lineDeriv
      simp
      apply instDerivLDO.linear_add
      · apply DifferentiableAt.comp
        simp; assumption
        apply DifferentiableAt.const_add
        apply DifferentiableAt.smul_const
        apply differentiableAt_id
      · apply DifferentiableAt.comp
        simp; assumption
        apply DifferentiableAt.const_add
        apply DifferentiableAt.smul_const
        apply differentiableAt_id
    }

  instance instPartialDerivLDO (i : Fin n) : LinearDifferentialOperator (𝕜:=𝕜) (E:=Euc 𝕜 n) (F:=F) (G:=F) (partialDeriv i) where
    linear_smul := by {
      intro c f x hf
      unfold partialDeriv
      apply (instLineDerivLDO _).linear_smul
      assumption
    }
    linear_add := by {
      intro f g x hf hg
      unfold partialDeriv
      apply (instLineDerivLDO _).linear_add
      assumption
      assumption
    }

instance instGradientLDO : LinearDifferentialOperator (𝕜:=𝕜) (E:=Euc 𝕜 n) (F:=𝕜) (G:=Euc 𝕜 n) (gradient) where
  linear_smul := by {
    intro c f x hf
    unfold gradient
    ext i
    apply (instPartialDerivLDO _).linear_smul
    assumption
  }
  linear_add := by {
    intro f g x hf hg
    unfold gradient
    ext i
    simp
    apply (instPartialDerivLDO _).linear_add <;>
    assumption
  }


end LinearDifferentialOperator

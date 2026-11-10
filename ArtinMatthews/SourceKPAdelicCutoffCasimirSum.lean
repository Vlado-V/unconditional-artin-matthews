module

public import ArtinMatthews.SourceKPAdelicCuspCutoff
public import ArtinMatthews.SourceKPAdelicRadialCasimir
public import ArtinMatthews.SourceKPAdelicArchHeightPaths
public import ArtinMatthews.SourceKPAdelicCutoffPathFinite
public import ArtinMatthews.SourceKPAdelicRadialPaths
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Differentiation of the actual finite cusp sum along its right
unipotent and diagonal paths. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Filter
open SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups BigOperators Topology ContDiff
noncomputable section

private theorem finitePath_derivatives {ι : Type*} [DecidableEq ι]
    (I J : Finset ι) (hIJ : I ⊆ J) (f : ℝ → ℂ) (F : ι → ℝ → ℂ)
    (he : f =ᶠ[𝓝 0] fun t => ∑ c ∈ I, F c t)
    (hz : ∀ c ∉ I, F c =ᶠ[𝓝 0] fun _ => 0)
    (hf : ∀ c, Differentiable ℝ (F c) ∧ Differentiable ℝ (deriv (F c))) :
    f 0 = ∑ c ∈ J, F c 0 ∧
      deriv f 0 = ∑ c ∈ J, deriv (F c) 0 ∧
        deriv (deriv f) 0 = ∑ c ∈ J, deriv (deriv (F c)) 0 := by
  have hfirst : deriv (fun t => ∑ c ∈ I, F c t) = fun t => ∑ c ∈ I, deriv (F c) t := by
    funext t
    exact deriv_fun_sum (fun c _ => (hf c).1 t)
  refine ⟨?_,?_,?_⟩
  · calc
      f 0 = ∑ c ∈ I, F c 0 := he.self_of_nhds
      _ = ∑ c ∈ J, F c 0 := Finset.sum_subset hIJ (fun c _ hc => (hz c hc).self_of_nhds)
  · calc
      deriv f 0 = ∑ c ∈ I, deriv (F c) 0 := by rw [he.deriv_eq,hfirst]
      _ = ∑ c ∈ J, deriv (F c) 0 := Finset.sum_subset hIJ (fun c _ hc => by
        simpa only [deriv_const] using (hz c hc).deriv_eq)
  · calc
      deriv (deriv f) 0 = ∑ c ∈ I, deriv (deriv (F c)) 0 := by
        rw [he.deriv.deriv_eq,hfirst]
        exact deriv_fun_sum (fun c _ => (hf c).2 0)
      _ = ∑ c ∈ J, deriv (deriv (F c)) 0 := Finset.sum_subset hIJ (fun c _ hc => by
        simpa only [deriv_const'] using (hz c hc).deriv.deriv_eq)

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicCutoffUpperTerm (T : ℝ) (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (v : InfinitePlace K) (z : ℂ) (c : SourceKPRationalBorelCoset K) (t : ℝ) : ℂ :=
  sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T s)
    (q*sourceArchGroupSingle K hζ v (sourceKPUpperMatrix ℂ ((t : ℂ)*z))) c

def sourceKPAdelicCutoffDiagonalTerm (T : ℝ) (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (v : InfinitePlace K) (c : SourceKPRationalBorelCoset K) (t : ℝ) : ℂ :=
  sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T s)
    (q*sourceArchGroupSingle K hζ v (sourceArchPositiveDiagonal t)) c

theorem sourceKPAdelicCutoffUpperTerm_mk (T : ℝ) (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (v : InfinitePlace K) (z : ℂ) (γ : PGL(2,K)) :
    sourceKPAdelicCutoffUpperTerm K hζ T s q v z (sourceKPRationalBorelCosetMk K γ) =
      sourceArchGlobalUpperTranslate K hζ
        (sourceKPAdelicRadialSection K hζ (sourceKPAdelicHeightCutoff T) s)
        (sourceKPAdelicProjectiveRationalLift K hζ γ*q) v z := by
  funext t
  change (sourceKPAdelicCutoffSeed K hζ T s).val
    (sourceKPAdelicProjectiveRationalLift K hζ γ*(q*sourceArchGroupSingle K hζ v _)) = _
  rw [← mul_assoc]
  rfl

theorem sourceKPAdelicCutoffDiagonalTerm_mk (T : ℝ) (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (v : InfinitePlace K) (γ : PGL(2,K)) :
    sourceKPAdelicCutoffDiagonalTerm K hζ T s q v (sourceKPRationalBorelCosetMk K γ) =
      sourceArchGlobalDiagonalTranslate K hζ
        (sourceKPAdelicRadialSection K hζ (sourceKPAdelicHeightCutoff T) s)
        (sourceKPAdelicProjectiveRationalLift K hζ γ*q) v := by
  funext t
  change (sourceKPAdelicCutoffSeed K hζ T s).val
    (sourceKPAdelicProjectiveRationalLift K hζ γ*(q*sourceArchGroupSingle K hζ v _)) = _
  rw [← mul_assoc]
  rfl

theorem sourceKPAdelicCutoffUpperTerm_twice (T : ℝ) (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (v : InfinitePlace K) (z : ℂ) (c : SourceKPRationalBorelCoset K) :
    Differentiable ℝ (sourceKPAdelicCutoffUpperTerm K hζ T s q v z c) ∧
      Differentiable ℝ (deriv (sourceKPAdelicCutoffUpperTerm K hζ T s q v z c)) := by
  induction c using Quotient.inductionOn with
  | _ γ =>
    have h := sourceKPAdelicRadialSection_upper_twice K hζ _ s
      ((sourceKPAdelicHeightCutoff_contDiff T).of_le (by simp))
      (sourceKPAdelicProjectiveRationalLift K hζ γ*q) v z
    rw [← sourceKPAdelicCutoffUpperTerm_mk] at h
    exact h

theorem sourceKPAdelicCutoffDiagonalTerm_twice (T : ℝ) (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (v : InfinitePlace K) (c : SourceKPRationalBorelCoset K) :
    Differentiable ℝ (sourceKPAdelicCutoffDiagonalTerm K hζ T s q v c) ∧
      Differentiable ℝ (deriv (sourceKPAdelicCutoffDiagonalTerm K hζ T s q v c)) := by
  induction c using Quotient.inductionOn with
  | _ γ =>
    have h := sourceKPAdelicRadialSection_diagonal_twice K hζ _ s
      ((sourceKPAdelicHeightCutoff_contDiff T).of_le (by simp))
      (sourceKPAdelicProjectiveRationalLift K hζ γ*q) v
    rw [← sourceKPAdelicCutoffDiagonalTerm_mk] at h
    exact h

def sourceKPAdelicCutoffCasimirTerm (T : ℝ) (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (v : InfinitePlace K) (c : SourceKPRationalBorelCoset K) : ℂ :=
  -(deriv (deriv (sourceKPAdelicCutoffUpperTerm K hζ T s q v 1 c)) 0 +
    deriv (deriv (sourceKPAdelicCutoffUpperTerm K hζ T s q v Complex.I c)) 0 +
    deriv (deriv (sourceKPAdelicCutoffDiagonalTerm K hζ T s q v c)) 0 -
    2*deriv (sourceKPAdelicCutoffDiagonalTerm K hζ T s q v c) 0)

theorem sourceKPAdelicCutoffCasimirTerm_mk (T : ℝ) (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (v : InfinitePlace K) (γ : PGL(2,K)) :
    sourceKPAdelicCutoffCasimirTerm K hζ T s q v (sourceKPRationalBorelCosetMk K γ) =
      sourceArchGlobalCasimir K hζ
        (sourceKPAdelicRadialSection K hζ (sourceKPAdelicHeightCutoff T) s)
        (sourceKPAdelicProjectiveRationalLift K hζ γ*q) v := by
  rw [sourceKPAdelicCutoffCasimirTerm,sourceKPAdelicCutoffUpperTerm_mk,
    sourceKPAdelicCutoffUpperTerm_mk,sourceKPAdelicCutoffDiagonalTerm_mk]
  rfl


theorem sourceKPAdelicCutoffCasimir_finite {T : ℝ} (hT : 0 < T)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) :
    ∃ J : Finset (SourceKPRationalBorelCoset K), ∀ s : ℂ,
      sourceArchGlobalCasimir K hζ (sourceKPAdelicCutoffEisenstein K hζ T s) q v =
        ∑ c ∈ J, sourceKPAdelicCutoffCasimirTerm K hζ T s q v c ∧
      sourceKPAdelicCutoffEisenstein K hζ T s q =
        ∑ c ∈ J, sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T s) q c ∧
      ∀ c ∉ J, sourceKPAdelicCutoffCasimirTerm K hζ T s q v c = 0 := by
  classical
  have hU (z : ℂ) : Continuous (fun t : ℝ => sourceKPUpperMatrix ℂ ((t : ℂ)*z)) :=
    sourceKPCutoffUpperMatrix_continuous.comp (Complex.continuous_ofReal.mul_const z)
  obtain ⟨I₁,h₁⟩ := sourceKPAdelicCutoff_path_finite_near K hζ hT q v _ (hU 1)
  obtain ⟨Iᵢ,hᵢ⟩ := sourceKPAdelicCutoff_path_finite_near K hζ hT q v _ (hU Complex.I)
  obtain ⟨Iₐ,hₐ⟩ := sourceKPAdelicCutoff_path_finite_near K hζ hT q v _ sourceKPCutoffPositiveDiagonal_continuous
  let J := (I₁ ∪ Iᵢ) ∪ Iₐ
  have h₁J : I₁ ⊆ J := Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  have hᵢJ : Iᵢ ⊆ J := Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  have hₐJ : Iₐ ⊆ J := Finset.subset_union_right
  refine ⟨J,fun s => ?_⟩
  have e₁ := finitePath_derivatives I₁ J h₁J
    (sourceArchGlobalUpperTranslate K hζ (sourceKPAdelicCutoffEisenstein K hζ T s) q v 1)
    (sourceKPAdelicCutoffUpperTerm K hζ T s q v 1) (h₁ s).1 (h₁ s).2
    (sourceKPAdelicCutoffUpperTerm_twice K hζ T s q v 1)
  have eᵢ := finitePath_derivatives Iᵢ J hᵢJ
    (sourceArchGlobalUpperTranslate K hζ (sourceKPAdelicCutoffEisenstein K hζ T s) q v Complex.I)
    (sourceKPAdelicCutoffUpperTerm K hζ T s q v Complex.I) (hᵢ s).1 (hᵢ s).2
    (sourceKPAdelicCutoffUpperTerm_twice K hζ T s q v Complex.I)
  have eₐ := finitePath_derivatives Iₐ J hₐJ
    (sourceArchGlobalDiagonalTranslate K hζ (sourceKPAdelicCutoffEisenstein K hζ T s) q v)
    (sourceKPAdelicCutoffDiagonalTerm K hζ T s q v) (hₐ s).1 (hₐ s).2
    (sourceKPAdelicCutoffDiagonalTerm_twice K hζ T s q v)
  refine ⟨?_,?_,?_⟩
  · unfold sourceArchGlobalCasimir
    rw [e₁.2.2,eᵢ.2.2,eₐ.2.2,eₐ.2.1]
    simp only [sourceKPAdelicCutoffCasimirTerm,Finset.sum_neg_distrib,Finset.sum_sub_distrib,
      Finset.sum_add_distrib,Finset.mul_sum]
  · simpa only [sourceArchGlobalUpperTranslate,sourceKPAdelicCutoffUpperTerm,Complex.ofReal_zero,
      zero_mul,sourceKPUpperMatrix_zero,sourceArchGroupSingle_one,mul_one] using e₁.1
  · intro c hc
    have hn₁ : c ∉ I₁ := fun h => hc (h₁J h)
    have hnᵢ : c ∉ Iᵢ := fun h => hc (hᵢJ h)
    have hnₐ : c ∉ Iₐ := fun h => hc (hₐJ h)
    have z₁ := ((h₁ s).2 c hn₁).deriv.deriv_eq
    have zᵢ := ((hᵢ s).2 c hnᵢ).deriv.deriv_eq
    have zₐ := ((hₐ s).2 c hnₐ).deriv.deriv_eq
    have zₐ' := ((hₐ s).2 c hnₐ).deriv_eq
    simp only [deriv_const'] at z₁ zᵢ zₐ zₐ'
    change deriv (deriv (sourceKPAdelicCutoffUpperTerm K hζ T s q v 1 c)) 0 = 0 at z₁
    change deriv (deriv (sourceKPAdelicCutoffUpperTerm K hζ T s q v Complex.I c)) 0 = 0 at zᵢ
    change deriv (deriv (sourceKPAdelicCutoffDiagonalTerm K hζ T s q v c)) 0 = 0 at zₐ
    change deriv (sourceKPAdelicCutoffDiagonalTerm K hζ T s q v c) 0 = 0 at zₐ'
    rw [sourceKPAdelicCutoffCasimirTerm,z₁,zᵢ,zₐ,zₐ']
    ring

end
end ArtinMatthews

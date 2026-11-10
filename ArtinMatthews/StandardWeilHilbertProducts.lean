module

public import ArtinMatthews.StandardAdelicWeilIndex
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceAdicLocalField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import ArtinMatthews.StandardAdelicWeilProduct
public import ArtinMatthews.StandardComplexWeil
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceAdicHilbertProductFormula
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine analytic and Hilbert products for the actual standard character.
The ratio has product one for independent proved reasons; no local/global
Weil or Hilbert equality is assumed. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain ClassFieldTheory
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]

theorem numberFieldQuadraticRoots : (primitiveRoots ((2 : ℕ+) : ℕ) F).Nonempty := by
  change (primitiveRoots 2 F).Nonempty
  exact ⟨-1, (mem_primitiveRoots (by decide : 0 < 2)).mpr
    (IsPrimitiveRoot.neg_one 0 (by decide))⟩

def finiteQuadraticHilbertSign (a b : Fˣ) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  ArtinMatthews.QuadraticGauss.rootSign F
    (GlobalHilbertPairingFamily.finiteFactor F
      (finitePlaceAdicHilbertPairingFamily F 2 (numberFieldQuadraticRoots F))
      (numberFieldQuadraticRoots F) v a b)

theorem finiteQuadraticHilbertSign_hasFiniteMulSupport (a b : Fˣ) :
    Function.HasFiniteMulSupport (finiteQuadraticHilbertSign F a b) :=
  ((finitePlaceAdicHilbertPairingFamily_productFormula F 2 (numberFieldQuadraticRoots F)).2.1 a b).fun_comp
    (ArtinMatthews.QuadraticGauss.rootSign F).map_one

theorem finiteQuadraticHilbertSign_finprod [IsTotallyComplex F] (a b : Fˣ) :
    ∏ᶠ v, finiteQuadraticHilbertSign F a b v = 1 := by
  let H : HeightOneSpectrum (𝓞 F) → rootsOfUnity 2 F := fun v =>
    GlobalHilbertPairingFamily.finiteFactor F
      (finitePlaceAdicHilbertPairingFamily F 2 (numberFieldQuadraticRoots F))
      (numberFieldQuadraticRoots F) v a b
  let I : InfinitePlace F → rootsOfUnity 2 F := fun v => globalInfinitePlaceHilbertSymbol F 2 v a b
  have h : (∏ v : InfinitePlace F, I v) * ∏ᶠ v, H v = 1 :=
    (finitePlaceAdicHilbertPairingFamily_productFormula F 2 (numberFieldQuadraticRoots F)).2.2 a b
  have hinf : (∏ v : InfinitePlace F, I v) = 1 := by
    apply Finset.prod_eq_one
    intro v _
    have hv : ¬ v.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v)
    change globalInfinitePlaceHilbertSymbol F 2 v a b = 1
    unfold globalInfinitePlaceHilbertSymbol
    split <;> rfl
  rw [hinf, one_mul] at h
  have hs : Function.HasFiniteMulSupport H :=
    (finitePlaceAdicHilbertPairingFamily_productFormula F 2 (numberFieldQuadraticRoots F)).2.1 a b
  calc
    _ = ∏ᶠ v, ArtinMatthews.QuadraticGauss.rootSign F (H v) := rfl
    _ = ArtinMatthews.QuadraticGauss.rootSign F (∏ᶠ v, H v) := (map_finprod _ hs).symm
    _ = 1 := by rw [h, map_one]

theorem finiteQuadraticHilbertSign_hasProd [IsTotallyComplex F] (a b : Fˣ) :
    HasProd (finiteQuadraticHilbertSign F a b) 1 := by
  have hs := finiteQuadraticHilbertSign_hasFiniteMulSupport F a b
  have hm : Multipliable (finiteQuadraticHilbertSign F a b) := multipliable_of_hasFiniteMulSupport hs
  have he : (∏' v, finiteQuadraticHilbertSign F a b v) = ∏ᶠ v, finiteQuadraticHilbertSign F a b v :=
    tprod_eq_finprod hs
  have h := hm.hasProd
  rw [he, finiteQuadraticHilbertSign_finprod F a b] at h
  exact h

def allPlaceQuadraticHilbertSign (a b : Fˣ) : ArchimedeanAdeles.Construction.Places F → ℂ
  | .inl _ => 1
  | .inr v => finiteQuadraticHilbertSign F a b v

theorem allPlaceQuadraticHilbertSign_hasProd [IsTotallyComplex F] (a b : Fˣ) :
    HasProd (allPlaceQuadraticHilbertSign F a b) 1 := by
  have h : HasProd (allPlaceQuadraticHilbertSign F a b) (1 * 1) :=
    HasProd.sum (f := allPlaceQuadraticHilbertSign F a b) hasProd_one
      (finiteQuadraticHilbertSign_hasProd F a b)
  simpa only [mul_one] using h

def globalWeilHilbertRatio (a b : Fˣ) (v : ArchimedeanAdeles.Construction.Places F) : ℂ :=
  (standardNormalizedWeil F a v * standardNormalizedWeil F b v) /
    (standardNormalizedWeil F (a * b) v * allPlaceQuadraticHilbertSign F a b v)

theorem globalWeilHilbertRatio_hasProd [IsTotallyComplex F] (a b : Fˣ) :
    HasProd (globalWeilHilbertRatio F a b) 1 := by
  have hn := (standardNormalizedWeil_hasProd F a).mul (standardNormalizedWeil_hasProd F b)
  have hd := (standardNormalizedWeil_hasProd F (a * b)).mul
    (allPlaceQuadraticHilbertSign_hasProd F a b)
  have h := hn.mul (hd.inv₀ (by simp))
  change HasProd (fun v => globalWeilHilbertRatio F a b v) 1
  simpa only [globalWeilHilbertRatio, div_eq_mul_inv, mul_one, inv_one] using h

theorem globalWeilHilbertRatio_infinite [IsTotallyComplex F] (a b : Fˣ) (v : InfinitePlace F) :
    globalWeilHilbertRatio F a b (.inl v) = 1 := by
  simp only [globalWeilHilbertRatio, standardNormalizedWeil_infinite,
    allPlaceQuadraticHilbertSign, one_mul, div_one]

end

end ArtinMatthews.QuadraticWeil

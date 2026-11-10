module

public import ArtinMatthews.SourceKPCoupledCylinderHaar
public import ArtinMatthews.SourceIntertwinerArchFinite
public import ArtinMatthews.SourceKPCoupledLocalProduct
public import ArtinMatthews.SourceKPAdelicKernelContinuity
public import ArtinMatthews.SourceKPCoupledWeylCompact
public import ArtinMatthews.SourceKPCoupledWildMask
public import ArtinMatthews.SourceKPLocalFiniteKernel
public import ArtinMatthews.SourceKPLocalRestBase
public import ArtinMatthews.SourceKubotaGL2Generation
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

/-! On the actual compact additive window the coupled kernel is the
indicator of the simultaneous deep cylinder. The phase-one Weyl
cancellation and the finite upper lift occur in the cover itself. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup SourcePhysical SourceArchJacquet
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing MatrixGroups Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Oᶠ" => IntegralAdeles.Construction.finiteIntegralRing K
local notation "g₀" => sourceKPCoupledWildWeyl K hζ
local notation "W₀" => sourceKPAdelicProjectiveWeyl K hζ

theorem sourceKPCoupledFiniteUpper_mem_compact (y : 𝔸ᶠ[K]) (hy : y ∈ Oᶠ)
    (hywild : ∀ P ∈ sixthWildPrimes K, y P = 0) :
    sourceKPAdelicUpperLift K hζ (0,y) ∈ sourceKPAdelicDeepCompact K hζ := by
  let g := (sourceKPGL2ProductEquiv K).symm (1, sourceKPUpperMatrix 𝔸ᶠ[K] y)
  have hg : sourceKPGL2ProductEquiv K g = (1, sourceKPUpperMatrix 𝔸ᶠ[K] y) :=
    (sourceKPGL2ProductEquiv K).apply_symm_apply _
  have hf (P : HeightOneSpectrum (𝓞 K)) : sourceKPAdelicBaseFiniteAt K P g = sourceGL2Upper (y P) := by
    change sourceKPAdeleMatrixAt K P (sourceKPGL2ProductEquiv K g).2 = _
    rw [hg, sourceKPAdeleMatrixAt_upper]
  have ha (v : InfinitePlace K) : sourceKPAdelicBaseComplexAt K hζ v g = 1 := by
    change sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K (sourceKPGL2ProductEquiv K g).1 v) = _
    rw [hg]
    simp only [map_one, Pi.one_apply]
  have hK : g ∈ sourceKPAdelicDeepCompactMatrix K hζ := by
    refine ⟨⟨?_, fun v => (ha v).symm ▸ sourceArchUnitaryGL.range.one_mem⟩, ?_⟩
    · intro P
      rw [hf]
      exact sourceKPIntegralMatrix_upper (sourceKPFiniteVal K P) (y P)
        ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K P).mp (hy P))
    · intro P hP
      rw [hf, hywild P ((mem_sixthWildPrimes P).mpr hP), sourceGL2Upper_zero]
      exact (sourceKPDeepLocalBase K P).range.one_mem
  refine ⟨⟨g,hK⟩, ?_⟩
  apply Prod.ext
  · change ProjGenLinGroup.mk (sourceKPGL2ProductEquiv K g).1 =
      ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) 0)
    rw [hg, sourceKPUpperMatrix_zero]
  · change sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPGL2ProductEquiv K g).2 =
      sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPUpperMatrix 𝔸ᶠ[K] y)
    rw [hg]

theorem sourceKPCoupledFiniteUpper_commutes (y : 𝔸ᶠ[K])
    (hywild : ∀ P ∈ sixthWildPrimes K, y P = 0) :
    Commute (sourceKPAdelicUpperLift K hζ (0,y)) g₀ := by
  unfold sourceKPCoupledWildWeyl sourceKPCoupledLocalProduct
  apply MonoidHom.commute_noncommPiCoprod
  intro P p
  apply Commute.symm
  apply sourceKPAdelicLocalProjective_commute_of_base_one K hζ P.val p
  have h := sourceKPAdelicLocalBase_upper K hζ P.val (show 𝔸[K] from (0,y))
  change sourceKPAdelicLocalBase K hζ P.val (sourceKPAdelicUpperLift K hζ (0,y)) =
    ProjGenLinGroup.mk (sourceGL2Upper (y P.val)) at h
  rw [h, hywild P.val P.property, sourceGL2Upper_zero, map_one]

theorem sourceKPCoupledZeroWild_mem_compact (y : 𝔸ᶠ[K]) (hy : y ∈ Oᶠ)
    (hywild : ∀ P ∈ sixthWildPrimes K, y P = 0) :
    W₀ * sourceKPAdelicUpperLift K hζ (0,y) * g₀ ∈ sourceKPAdelicDeepCompact K hζ := by
  rw [mul_assoc, (sourceKPCoupledFiniteUpper_commutes K hζ y hywild).eq, ← mul_assoc]
  exact (sourceKPAdelicDeepCompact K hζ).mul_mem (sourceKPCoupledWildWeyl_cancel_mem K hζ)
    (sourceKPCoupledFiniteUpper_mem_compact K hζ y hy hywild)

theorem sourceKPCoupledCompactKernel_zero_wild (s : ℂ) (y : 𝔸ᶠ[K]) (hy : y ∈ Oᶠ)
    (hywild : ∀ P ∈ sixthWildPrimes K, y P = 0) :
    sourceKPFiniteIntertwiningKernel K hζ s (g₀).2 y = 1 := by
  let k : sourceKPAdelicDeepCompact K hζ :=
    ⟨W₀ * sourceKPAdelicUpperLift K hζ (0,y) * g₀,
      sourceKPCoupledZeroWild_mem_compact K hζ y hy hywild⟩
  have hg : g₀ = (1,(g₀).2) := Prod.ext (sourceKPCoupledWildWeyl_arch K hζ) rfl
  have hk := sourceKPAdelicCompactScalar_right K hζ s 1 k
  rw [one_mul, sourceKPAdelicCompactScalar_one] at hk
  rw [← sourceKPLocalFiniteKernel_eq_full K hζ s (g₀).2 y, ← hg]
  exact hk

theorem sourceKPCoupledCompactKernel_indicator (s : ℂ) (x : 𝔸ᶠ[K]) (hx : x ∈ Oᶠ) :
    sourceKPFiniteIntertwiningKernel K hζ s (g₀).2 x =
      (sourceKPCoupledDeepCylinder K (sixthWildPrimes K)).indicator (fun _ => (1 : ℂ)) x := by
  let T := sixthWildPrimes K
  let y := sourceKPCoupledZeroPlaces K T x
  have hy : y ∈ Oᶠ := by
    intro P
    change sourceKPCoupledZeroPlaces K T x P ∈ P.adicCompletionIntegers K
    rw [sourceKPCoupledZeroPlaces_at]
    split_ifs
    · exact (P.adicCompletionIntegers K).zero_mem
    · exact hx P
  have hywild (P : HeightOneSpectrum (𝓞 K)) (hP : P ∈ T) : y P = 0 := by
    change sourceKPCoupledZeroPlaces K T x P = 0
    rw [sourceKPCoupledZeroPlaces_at, ite_eq_left hP]
  rw [sourceKPCoupledWildKernel_mask K hζ T (Finset.Subset.refl T), sourceKPCoupledCompactKernel_zero_wild K hζ s y hy hywild,
    mul_one]
  by_cases h : ∀ P ∈ T, x P ∈ sourceKPDeepIdealImage K P
  · rw [Set.indicator_of_mem (show x ∈ sourceKPCoupledDeepCylinder K T from ⟨hx,h⟩)]
    apply Finset.prod_eq_one
    intro P hP
    exact Set.indicator_of_mem (h P hP) _
  · rw [Set.indicator_of_notMem (show x ∉ sourceKPCoupledDeepCylinder K T from fun hx' => h hx'.2)]
    push_neg at h
    obtain ⟨P,hP,hxP⟩ := h
    exact Finset.prod_eq_zero hP (Set.indicator_of_notMem hxP _)

end
end ArtinMatthews

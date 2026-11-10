module

public import ArtinMatthews.SourceFiniteFiberScattering
public import ArtinMatthews.SourceArchIntertwinerProduct
public import ArtinMatthews.SourceFiniteIntertwinerEuler
public import ArtinMatthews.SourceFiniteIntertwinerIntegrable
public import ArtinMatthews.SourceFiniteProjectiveSupport
public import ArtinMatthews.SourceFiniteWindowTameStep
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

/-! One actual finite Euler window can be used for an entire finite family
of translated fibers. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical
open scoped NumberField AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Places" => HeightOneSpectrum (𝓞 K)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Initial" => fun s : ℂ => ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * Complex.re s + 1

theorem sourceKPFiniteFiberScatteringContinuation_eq_of_compactRepresentative
    (a : SourceKPFiniteAdeleCover K hζ) (S : Finset Places)
    (hH : sourceHilbertSet K ∅ ⊆ S) (hB : traceBadPlaces K ⊆ S)
    (hcompact : ∀ Q ∉ S, (6 : 𝓞 K) ∉ Q.asIdeal ∧
      ∃ k : SourceFiniteKP2Integral K Q, k.val = sourceKPAdeleMatrixAt K Q a.base)
    {s : ℂ} (hs : Initial s) :
    sourceKPAdelicTraceIntertwiner K hζ s (1, sourceKPFiniteAdeleProjectiveMk K hζ a) =
      sourceKPFiniteFiberScatteringContinuation K hζ (sourceKPFiniteAdeleProjectiveMk K hζ a) S s := by
  let g := sourceKPFiniteAdeleProjectiveMk K hζ a
  have hex := sourceKPInitialHalfplane_exterior K hs
  have hpos : 0 < s.re := lt_trans (by norm_num) hex
  have hf := sourceKPFiniteIntertwiningKernel_integrable K hζ hs g
  have he : sourceKPFiniteIntertwiner K hζ s g = sourceKPExteriorScattering S s *
      sourceKPFiniteWindowIntegral K (sourceKPFiniteIntertwiningKernel K hζ s g) S := by
    apply sourceKPFiniteWindowIntegral_eq_product_limit K S _ hf
      (fun Q => sourceKPUnramifiedScatteringFactor Q s) _
      (sourceKPUnramifiedScatteringFactor_hasProd_all K S hex)
    intro T Q hQT hQS
    let Q' : SourceExteriorPrime K ∅ := ⟨Q, fun h => hQS (hH h)⟩
    obtain ⟨h6, k, hk⟩ := hcompact Q hQS
    exact sourceKPFiniteWindowIntertwiner_tame_step_integralRepresentative K hζ hpos
      T Q' hQT (fun h => hQS (hB h)) h6 a k hk
  change sourceKPAdelicTraceIntertwiner K hζ s (1, g) =
    sourceKPFiniteFiberScatteringContinuation K hζ g S s
  simpa only [sourceKPFiniteFiberScatteringContinuation, he] using
    sourceKPAdelicTraceIntertwiner_at_finite K hζ hpos g

theorem sourceKPFiniteFiberScatteringContinuation_common_window
    {I : Type*} [Fintype I] (g : I → Gf) (S₁ : Finset Places) :
    ∃ S : Finset Places, S₁ ⊆ S ∧ sourceHilbertSet K ∅ ⊆ S ∧ traceBadPlaces K ⊆ S ∧
      ∀ i (s : ℂ), Initial s → sourceKPAdelicTraceIntertwiner K hζ s (1, g i) =
        sourceKPFiniteFiberScatteringContinuation K hζ (g i) S s := by
  choose a T ha _ _ hcompact using fun i : I =>
    sourceKPFiniteProjective_support_compact K hζ (g i) ∅
  let S := S₁ ∪ (sourceHilbertSet K ∅ ∪ (traceBadPlaces K ∪ Finset.univ.biUnion T))
  have hH : sourceHilbertSet K ∅ ⊆ S := Finset.subset_union_left.trans Finset.subset_union_right
  have hB : traceBadPlaces K ⊆ S :=
    Finset.subset_union_left.trans (Finset.subset_union_right.trans Finset.subset_union_right)
  refine ⟨S, Finset.subset_union_left, hH, hB, ?_⟩
  intro i s hs
  have hTi : T i ⊆ S := by
    intro Q hQ
    exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hQ⟩)))
  rw [← ha i]
  exact sourceKPFiniteFiberScatteringContinuation_eq_of_compactRepresentative K hζ (a i) S hH hB
    (fun Q hQ => hcompact i Q (fun h => hQ (hTi h))) hs

end
end ArtinMatthews

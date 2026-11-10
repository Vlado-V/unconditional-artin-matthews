module

public import ArtinMatthews.SourceKPRetainedSeedVector
public import ArtinMatthews.SourceKPCuspResidualFourierRelation
public import ArtinMatthews.SourceKPCuspResidualFourierSymmetries
public import ArtinMatthews.SourceKPLocalBorelEmbedding
public import ArtinMatthews.SourceKPResidualRetainedNonzero
public import ArtinMatthews.SourceKPRetainedCutoff
public import ArtinMatthews.SourceKPRetainedDiagonalFix
public import ArtinMatthews.SourceKPRetainedExteriorDiagonal
public import ArtinMatthews.SourceKPRetainedTinySixth
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

/-! A fixed depth can be imposed on every retained local cutoff.
The same finite average then has literal support inside local sixth powers. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix StandardAdelic SourcePhysical SourceReflection QuadraticWeil
open scoped NumberField MatrixGroups AdeleRing SourcePhysical Classical BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Kf" => sourceKPFiniteLevelSubgroup K hζ
local notation "D" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ
local notation "unitAt" => sourceKPRetainedUnitAt K
local notation "tuple" => sourceKPAdelicRootSupportTuple K hζ
local notation "diag" => sourceKPDiagonalHom 𝔸ᶠ[K]

private theorem tuple_conjugate_level (U : Finset Pr) (a : 𝔸ᶠ[K]ˣ) (qf : Gf)
    (h : ∀ P ∈ U, qf⁻¹*D (sourceKPAdeleLocalUnit K P (unitAt P a))*qf ∈ Kf) :
    qf⁻¹*(tuple 1 (diag a) U).2*qf ∈ Kf := by
  induction U using Finset.induction_on with
  | empty =>
    have he : (tuple 1 (diag a) (∅ : Finset Pr)).2 = 1 :=
      (sourceKPFiniteAdeleProjectiveMk K hζ).map_one
    rw [he,mul_one,inv_mul_cancel]
    exact (Kf).one_mem
  | @insert P U hP ih =>
    let v := (tuple 1 (diag a) U).2
    let w := D (sourceKPAdeleLocalUnit K P (unitAt P a))
    have he : (tuple 1 (diag a) (insert P U)).2 = v*w := by
      rw [congrArg Prod.snd (sourceKPAdelicRootSupportTuple_insert K hζ 1 (diag a) U P hP)]
      change v*(sourceKPAdelicLocalProjective K hζ P
        (sourceFiniteKP2ProjectiveLift K hζ P (sourceKPAdeleMatrixAt K P (diag a)))).2 = v*w
      rw [sourceKPAdeleMatrixAt_diagonal, sourceKPAdelicLocalProjective_diagonal]
      rfl
    rw [he, show qf⁻¹*(v*w)*qf = (qf⁻¹*v*qf)*(qf⁻¹*w*qf) by group]
    exact (Kf).mul_mem (ih fun Q hQ => h Q (Finset.mem_insert_of_mem hQ))
      (h P (Finset.mem_insert_self _ _))

private theorem retained_conjugate_level (S : Finset Pr) (z : ∀ P : S, (P.val.adicCompletion K)ˣ)
    (qf : Gf) (hz : ∀ P : S, qf⁻¹*D (sourceKPAdeleLocalUnit K P.val (z P))*qf ∈ Kf) :
    qf⁻¹*D (sourceKPRetainedDiagonalUnit K S z)*qf ∈ Kf := by
  let a := sourceKPRetainedDiagonalUnit K S z
  have hunit : sourceKPRetainedUnitPart K S a = a := by
    unfold sourceKPRetainedUnitPart
    apply congrArg (sourceKPRetainedDiagonalUnit K S)
    funext P
    exact sourceKPRetainedDiagonalUnit_unitAt_mem K S z P
  change qf⁻¹*D a*qf ∈ Kf
  rw [← hunit, sourceKPRetainedDiagonalLift_unitPart_eq_tuple]
  apply tuple_conjugate_level
  intro P hP
  have he : unitAt P a = z ⟨P,hP⟩ := sourceKPRetainedDiagonalUnit_unitAt_mem K S z ⟨P,hP⟩
  rw [he]
  exact hz ⟨P,hP⟩

theorem sourceKPRetainedPositiveSeed_exists_at_depth
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (depth : sourceHilbertSet K S₀ → ℕ) {T : ℝ} (hT : 2 < T) :
    let S := sourceHilbertSet K S₀
    ∃ (a : GL (Fin 2) 𝔸ᶠ[K]) (R M : S → ℕ) (U : ∀ P : S, SourceThetaFiniteCutoff K P.val),
      let q₀ := (tuple 1 a S).2
      let C := sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le)
      C q₀ ≠ 0 ∧ sourceKPRetainedSeedVector K hζ S R M hT q₀ ≠ 0 ∧
      (∀ (P : S) (t : (P.val.adicCompletion K)ˣ), t ∈ (U P).region →
        ((t : P.val.adicCompletion K)-1) ∈ sourceLocalBall K P.val (-(depth P:ℤ)) ∧
          ∃ w, w^6 = t) ∧
      ∀ z : ∀ P : S, (P.val.adicCompletion K)ˣ,
        sourceKPRetainedSeedCoefficient K hζ S R M (one_le_two.trans hT.le) q₀ z =
          C q₀ * ∏ P : S, (U P).factor (z P) := by
  let S := sourceHilbertSet K S₀
  obtain ⟨a,hne⟩ := sourceKPResidualFourierValue_retained_exists_ne_zero K hζ S₀ hS hT
  let q₀ := (tuple 1 a S).2
  let hT' : 1 ≤ T := one_le_two.trans hT.le
  let C := sourceKPCuspResidualFourierValue K hζ 1 hT'
  choose M hM hperiod using fun P : S => sourceKPRetained_upper_period K hζ P.val q₀
  choose D₀ hD₀ hdiag using fun P : S => sourceKPRetained_small_diagonal_level K hζ P.val q₀
  choose J hJ hSixth using fun P : S => sourceKPRetained_tiny_sixth K P.val
  let N (P : S) := max (max (D₀ P) (J P)) (depth P)
  let R (P : S) : ℕ := sourceDifferentExponent K P.val + N P + 1
  let n (P : S) : ℤ := (sourceDifferentExponent K P.val:ℤ) - (R P:ℤ)
  have hnN (P : S) (k : ℕ) (hk : k ≤ N P) : n P ≤ -(k : ℤ) := by
    dsimp [n,R]
    omega
  have hND (P : S) : D₀ P ≤ N P := (le_max_left _ _).trans (le_max_left _ _)
  have hNJ (P : S) : J P ≤ N P := (le_max_right _ _).trans (le_max_left _ _)
  have hn (P : S) : n P < 0 := (hnN P (D₀ P) (hND P)).trans_lt (by have := hD₀ P; omega)
  let U (P : S) := sourceKPRetainedCutoff K P.val (n P) (hn P)
  have hsmall (P : S) (t : (P.val.adicCompletion K)ˣ) (ht : t ∈ (U P).region)
      (k : ℕ) (hk : k ≤ N P) :
      ((t : P.val.adicCompletion K)-1) ∈ sourceLocalBall K P.val (-(k:ℤ)) := by
    change (t : P.val.adicCompletion K)-1 ∈ sourceLocalBall K P.val (n P) at ht
    exact ht.trans (WithZero.exp_le_exp.mpr (hnN P k hk))
  have hfix (P : S) (t : (P.val.adicCompletion K)ˣ) (ht : t ∈ (U P).region) :
      q₀⁻¹*D (sourceKPAdeleLocalUnit K P.val t)*q₀ ∈ Kf :=
    (hdiag P t (hsmall P t ht (D₀ P) (hND P))).2
  have hcut (z : ∀ P : S, (P.val.adicCompletion K)ˣ) :
      sourceKPRetainedSeedCoefficient K hζ S R M hT' q₀ z =
        C q₀ * ∏ P : S, (U P).factor (z P) := by
    rw [sourceKPRetainedSeedCoefficient_eq K hζ S R M hT' q₀ hperiod z]
    have hprod : (∏ P : S, (U P).factor (z P)) = ∏ P : S,
        if (z P : P.val.adicCompletion K)-1 ∈ sourceLocalBall K P.val (n P) then 1 else 0 :=
      Finset.prod_congr rfl (fun P _ => sourceKPRetainedCutoff_factor K P.val (n P) (hn P) (z P))
    change C (D (sourceKPRetainedDiagonalUnit K S z)*q₀) * _ = C q₀ * _
    rw [← hprod]
    by_cases hz : ∀ P : S, z P ∈ (U P).region
    · have hl := retained_conjugate_level K hζ S z q₀ (fun P => hfix P (z P) (hz P))
      have he : C (D (sourceKPRetainedDiagonalUnit K S z)*q₀) = C q₀ := calc
        _ = C (q₀*(q₀⁻¹*D (sourceKPRetainedDiagonalUnit K S z)*q₀)) :=
          congrArg C (by group)
        _ = _ := sourceKPCuspResidualFourierValue_right_level K hζ 1 hT' q₀ _ hl
      rw [he]
    · obtain ⟨P,hP⟩ := not_forall.mp hz
      have hzero : (∏ P : S, (U P).factor (z P)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ P) (Set.indicator_of_notMem hP _)
      rw [hzero,mul_zero,mul_zero]
  refine ⟨a,R,M,U,hne,?_,fun P t ht => ⟨hsmall P t ht (depth P) (le_max_right _ _),
    hSixth P t (hsmall P t ht (J P) (hNJ P))⟩,hcut⟩
  intro hzero
  let z : ∀ P : S, (P.val.adicCompletion K)ˣ := fun _ => 1
  have hz := hcut z
  have hfac (P : S) : (U P).factor (z P) = 1 := Set.indicator_of_mem (U P).one_mem _
  simp only [hfac, Finset.prod_const_one, mul_one] at hz
  have hC : sourceKPRetainedSeedCoefficient K hζ S R M hT' q₀ z = 0 :=
    sourceKPCuspResidualFourierValue_sum_eq_zero_of_translateCombination K hζ
      (sourceKPRetainedSeedLevel K hζ S R M q₀)
      (sourceKPRetainedSeedTranslate K hζ S R M q₀)
      (sourceKPRetainedSeedLevel_le_conjugate K hζ S R M q₀)
      (sourceKPRetainedSeedWeight K S R M) hT hzero 1
      (D (sourceKPRetainedDiagonalUnit K S z))
  exact hne (hz.symm.trans hC)

end
end ArtinMatthews

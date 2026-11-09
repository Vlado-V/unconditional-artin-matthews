module

public import ArtinMatthews.MarkedPhysicalCoprimeScalarDetector
public import ArtinMatthews.MarkedTypeIISharedMajorReindex
public import ArtinMatthews.MarkedTypeIISharedMajorSource


set_option backward.privateInPublic true
@[expose] public section

/-! Identification of the physical scalar major detector with the coprime
part of the original scalar major sum. Character absorption and cutoff
restriction use the literal endpoint rectangles. -/
namespace ArtinMatthews
noncomputable section
open Finset
open scoped ComplexConjugate

theorem markedPhysicalScalarDetectorTerm_major
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (Q Y : ℝ)
    (α β : ℕ → ℂ) (b a : ℕ) (v w : ℕ×ℕ) :
    markedPhysicalScalarDetectorTerm η Y (markedRawEdgeMajorDetector ψ Q Y) α β b a v w =
      markedTypeIIScalarMajorTerm η ψ Q Y α β b a v w := by
  dsimp only [markedPhysicalScalarDetectorTerm,markedPhysicalScalarCofactorTerm,
    markedRawEdgeMajorDetector,markedTypeIIScalarMajorTerm,markedMajorIntegerDeterminant]
  ring

theorem markedPhysicalCoprimeScalarDetectorSum_sub
    {J : Type*} [Fintype J] (P : J → Finset ℕ) (S N : Finset ℕ)
    (η : ℝ → ℂ) (Y : ℝ) (first second : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ) :
    markedPhysicalCoprimeScalarDetectorSum P S N η Y (first-second) α β =
      markedPhysicalCoprimeScalarDetectorSum P S N η Y first α β -
      markedPhysicalCoprimeScalarDetectorSum P S N η Y second α β := by
  simp only [markedPhysicalCoprimeScalarDetectorSum,markedPhysicalScalarDetectorBlock,
    markedPhysicalScalarDetectorTerm,markedPhysicalScalarCofactorTerm,Pi.sub_apply,
    mul_sub,sub_mul,sum_sub_distrib]

theorem markedPhysicalCoprimeScalarDetectorSum_minor_split
    {J : Type*} [Fintype J] (P : J → Finset ℕ) (S N : Finset ℕ)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (Q Y : ℝ) (α β : ℕ → ℂ) :
    markedPhysicalCoprimeScalarDetectorSum P S N η Y (markedBanEdgeKernel ψ Q Y) α β =
      markedPhysicalCoprimeScalarDetectorSum P S N η Y (markedRawEdgeDeltaDetector ψ Y) α β -
      markedPhysicalCoprimeScalarDetectorSum P S N η Y (markedRawEdgeMajorDetector ψ Q Y) α β := by
  have h : markedBanEdgeKernel ψ Q Y =
      markedRawEdgeDeltaDetector ψ Y-markedRawEdgeMajorDetector ψ Q Y := by
    funext b a t
    simp only [markedBanEdgeKernel,markedRawEdgeDeltaDetector,markedRawEdgeMajorDetector,Pi.sub_apply,mul_sub]
  rw [h,markedPhysicalCoprimeScalarDetectorSum_sub]

theorem markedPhysicalCoprimeScalarDetectorSum_major_on
    {J : Type*} [Fintype J] (P : J → Finset ℕ) (S N : Finset ℕ)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (Q Y : ℝ) (α β : ℕ → ℂ) :
    markedPhysicalCoprimeScalarDetectorSum P S N η Y (markedRawEdgeMajorDetector ψ Q Y) α β =
      markedTypeIIScalarMajorOn P (markedPhysicalCoprimeLabelPairs P) S S N η ψ Q Y α β
        (fun _ _ _ => 1) := by
  simp only [markedPhysicalCoprimeScalarDetectorSum,markedPhysicalScalarDetectorBlock,
    markedTypeIIScalarMajorOn,markedPhysicalScalarDetectorTerm_major,one_mul,product_eq_sprod]

theorem markedPhysicalCoprimeScalarDetectorSum_fixed_major
    {J : Type*} [Fintype J] (P : J → Finset ℕ) {Mχ : ℕ} (ξ : DirichletCharacter ℂ Mχ)
    (S : Finset ℕ) (l r : ℕ) (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ)
    (Q Y W modulation : ℝ) (β : ℕ → ℂ)
    (hY : 0 < Y) (hη : Function.support η ⊆ Set.Icc 1 4) :
    markedPhysicalCoprimeScalarDetectorSum P S (Icc l r) η Y (markedRawEdgeMajorDetector ψ Q Y)
      (fun m => ξ (m:ℕ)*markedMajorCenteredCoefficient W modulation m)
      (fun n => ξ (n:ℕ)*β n) =
      markedMajorFixedDyadPairSum P η ψ Q Y W modulation S S l r β ξ (fun z => z.1.Coprime z.2) := by
  classical
  let α := markedMajorCenteredCoefficient W modulation
  let G : (ℕ×ℕ) → (ℕ×ℕ) → (ℕ×ℕ) → ℂ :=
    fun _ v w => ξ (v.1*v.2:ℕ)*conj (ξ (w.1*w.2:ℕ))
  let E : (ℕ×ℕ) → Prop := fun z => z.1.Coprime z.2
  have hL : markedPhysicalCoprimeLabelPairs P =
      (markedMajorLabelSet P×ˢmarkedMajorLabelSet P).filter E := by
    ext z
    simp only [markedPhysicalCoprimeLabelPairs,product_eq_sprod,mem_filter,E]
  calc
    _ = markedTypeIIScalarMajorOn P (markedPhysicalCoprimeLabelPairs P) S S (Icc l r)
        η ψ Q Y α β G := by
      rw [markedPhysicalCoprimeScalarDetectorSum_major_on]
      simp only [markedTypeIIScalarMajorOn,one_mul]
      apply congrArg (fun t : ℂ => (markedMajorLabelMass P:ℂ)^2*t)
      apply sum_congr rfl
      intro z _
      apply sum_congr rfl
      intro v _
      apply sum_congr rfl
      intro w _
      exact markedTypeIIScalarMajorTerm_character η ψ Q Y α β ξ z.1 z.2 v w
    _ = markedTypeIIScalarMajorOn P
        ((markedTypeIIDyadLabels P Y×ˢmarkedTypeIIDyadLabels P Y).filter E) S S (Icc l r)
          η ψ Q Y α β G := by
      rw [hL]
      exact markedTypeIIScalarMajorOn_filtered_dyad P E S S (Icc l r) η ψ Q Y α β G hY hη
    _ = _ := by
      unfold markedMajorFixedDyadPairSum
      apply congrArg (fun pairs : Finset (ℕ×ℕ) =>
        markedTypeIIScalarMajorOn P pairs S S (Icc l r) η ψ Q Y α β G)
      ext z
      simp only [mem_filter,E]

theorem markedPhysicalScalar_fixed_delta_sub_major_eq
    {J : Type*} [Fintype J] (P : J → Finset ℕ) {Mχ : ℕ} (ξ : DirichletCharacter ℂ Mχ)
    (S : Finset ℕ) (l r : ℕ) (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ)
    (Q Y W modulation : ℝ) (β : ℕ → ℂ)
    (hY : 0 < Y) (hη : Function.support η ⊆ Set.Icc 1 4) :
    let αχ := fun m => ξ (m:ℕ)*markedMajorCenteredCoefficient W modulation m
    let βχ := fun n => ξ (n:ℕ)*β n
    markedPhysicalCoprimeScalarDetectorSum P S (Icc l r) η Y (markedRawEdgeDeltaDetector ψ Y) αχ βχ -
      markedMajorFixedIntervalPairSum P ξ η ψ Q Y W modulation S S l r β =
    markedPhysicalCoprimeScalarDetectorSum P S (Icc l r) η Y (markedBanEdgeKernel ψ Q Y) αχ βχ -
      markedMajorFixedDyadPairSum P η ψ Q Y W modulation S S l r β ξ (fun z => ¬z.1.Coprime z.2) := by
  dsimp only
  rw [markedPhysicalCoprimeScalarDetectorSum_minor_split,
    markedPhysicalCoprimeScalarDetectorSum_fixed_major P ξ S l r η ψ Q Y W modulation β hY hη,
    markedMajorFixedIntervalPairSum_eq_coprime_add_shared P η ψ Q Y W modulation S S l r β ξ hY hη]
  ring

end
end ArtinMatthews

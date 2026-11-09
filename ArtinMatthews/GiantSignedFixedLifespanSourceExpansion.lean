module

public import ArtinMatthews.GiantSignedLifespanOriginalPathFinite
public import ArtinMatthews.GiantSignedFixedLifespanSourceWeight
public import ArtinMatthews.GiantTwoSidedResidueDensity


set_option backward.privateInPublic true
@[expose] public section

/-! Finite expansion of the original independent Fourier moment into
its actual guarded paths and supported prime-lifespan choices. -/

namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

local notation "Bands" => Sum.elim PS PB
local notation "Pattern" => giantSignedChronologicalJoinedPattern (S := S) C
local notation "Slots" => GiantSignedLifespanPathSlots PS PB ell C
local notation "Raw" => GiantSignedLifespanRawPath PS PB ell C
local notation "Labels" => Fin (n+1) → MarkedPhysicalMarking Bands (k+ell)
local notation "Roots" => GiantTwoSidedFullResidue PS

private abbrev fixedLifespanBaseline (PB : B → Finset ℕ) (q : ℝ) (n : ℕ) : ℝ :=
  ∏ p : ↥(markedPhysicalBandPrimes PB), giantSignedPrimeResidueBaseline p.val (markedMemoryVisitQ q n)

private def fixedLifespanRawTerm (raw : Raw) (κ : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell) (θ : AddCircle (1 : ℝ)) : ℂ :=
  ∑ c : {c : GiantSignedJoinedBigLifespanChoice raw.2.1 //
      GiantSignedJoinedBigLifespanSupported raw.2.1 (raw.offset κ) (markedMemoryVisitQ q n) c},
    giantTwoSidedRootScalar Pattern raw.2.1 raw.1.1 raw.1.2.1 raw.1.2.2 ζ
      (fun i => giantSignedJoinedCoefficient (PS := PS) (K i)) *
    ((giantTwoSidedIndependentResidueFactor PS (giantSignedSmallMarking raw.2.1) q
      (raw.offset κ) raw.2.2 / Fintype.card Roots : ℝ) : ℂ) *
    fourier (raw.offset κ (Fin.last n)) θ *
    (giantSignedJoinedBigLifespanNormalizedProduct raw.2.1 (raw.offset κ) (markedMemoryVisitQ q n) c.val : ℂ)

variable [hPB : ∀ p : ↥(markedPhysicalBandPrimes PB), NeZero p.val]
    [hBands : ∀ p : ↥(markedPhysicalBandPrimes (Sum.elim PS PB)), NeZero p.val]

private theorem fixedLifespanSlots_sum (slots : Slots) (κ : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell) (θ : AddCircle (1 : ℝ))
    (hdis : Pairwise (fun g h : S ⊕ B => Disjoint (Bands g) (Bands h)))
    (hb : ∀ p : ↥(markedPhysicalBandPrimes PB),
      giantSignedPrimeResidueBaseline p.val (markedMemoryVisitQ q n) ≠ 0) :
    giantTwoSidedIndependentFourierMoment Pattern slots.1 slots.2.1 slots.2.2 κ q ζ
        (fun i => giantSignedJoinedCoefficient (PS := PS) (K i)) θ =
      (fixedLifespanBaseline PB q n : ℂ)*
        ∑ labels : Labels, ∑ r : Roots,
          if GiantSignedLifespanRawPath.valid (PS := PS) (PB := PB) (ell := ell) (C := C) ⟨slots,labels,r⟩ κ then
            fixedLifespanRawTerm (⟨slots,labels,r⟩ : Raw) κ q ζ K θ else 0 := by
  unfold giantTwoSidedIndependentFourierMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro labels _
  let raw (r : Roots) : Raw := ⟨slots,labels,r⟩
  let offset := giantTwoSidedPathOffset
    (giantTwoSidedLabelIncrement (ell := ell) Pattern labels slots.1 slots.2.2 κ)
  let scalar := giantTwoSidedRootScalar Pattern labels slots.1 slots.2.1 slots.2.2 ζ
    (fun i => giantSignedJoinedCoefficient (PS := PS) (K i))
  let phase := fourier (offset (Fin.last n)) θ
  let static := GiantTwoSidedStaticLabels Pattern slots.1 slots.2.1 slots.2.2 labels
  let compatible := GiantTwoSidedActiveCompatible univ labels offset
  let active (r : Roots) := GiantSignedFullPrimeActive (giantSignedSmallMarking labels) offset r
  let vq := markedMemoryVisitQ q n
  let Choices := {c : GiantSignedJoinedBigLifespanChoice labels //
    GiantSignedJoinedBigLifespanSupported labels offset vq c}
  let small (r : Roots) : ℝ := giantTwoSidedIndependentResidueFactor PS
    (giantSignedSmallMarking labels) q offset r / Fintype.card Roots
  let big (c : Choices) : ℝ := giantSignedJoinedBigLifespanNormalizedProduct labels offset vq c.val
  change (if static then scalar*(giantTwoSidedIndependentResidueMean labels q offset : ℂ)*phase else 0) =
    (fixedLifespanBaseline PB q n : ℂ)*∑ r : Roots,
      if (raw r).valid κ then fixedLifespanRawTerm (raw r) κ q ζ K θ else 0
  by_cases hs : static
  · by_cases hc : compatible
    · have hv (r : Roots) : (raw r).valid κ ↔ active r := by
        change (static ∧ compatible ∧ active r) ↔ active r
        simp only [hs,hc,true_and]
      have hterm (r : Roots) :
          (if (raw r).valid κ then fixedLifespanRawTerm (raw r) κ q ζ K θ else 0) =
            ∑ c : Choices, scalar*(small r : ℂ)*phase*(big c : ℂ) := by
        by_cases ha : active r
        · rw [ite_eq_left ((hv r).mpr ha)]
          rfl
        · rw [ite_eq_right (fun h => ha ((hv r).mp h))]
          have hz : small r = 0 := by
            unfold small
            rw [giantTwoSidedIndependentResidueFactor_zero PS (giantSignedSmallMarking labels) q offset r ha,
              zero_div]
          simp only [hz,Complex.ofReal_zero,mul_zero,zero_mul,Finset.sum_const_zero]
      have hS : Pairwise (fun s t => Disjoint (PS s) (PS t)) := fun s t hne =>
        hdis (fun h => hne (Sum.inl.inj h))
      have hmean : giantTwoSidedIndependentResidueMean labels q offset =
          (∑ r : Roots, small r) * fixedLifespanBaseline PB q n * ∑ c : Choices, big c := by
        rw [giantSignedSourceResidueMean_small_big_supported labels hdis offset q hb,
          giantSignedFullPrimeResidueMean_eq_source hS]
        simp only [giantTwoSidedIndependentResidueMean,small,big,fixedLifespanBaseline,vq,Finset.sum_div] <;>
          congr 1 <;>
          exact Finset.sum_congr (congrArg (@Finset.univ Choices) (Subsingleton.elim _ _)) (fun _ _ => rfl)
      simp only [hs,ite_true,hterm,hmean,Complex.ofReal_mul,Complex.ofReal_sum]
      calc
        _ = (fixedLifespanBaseline PB q n : ℂ)*
            ((scalar*(∑ r : Roots, (small r : ℂ)))*phase*(∑ c : Choices, (big c : ℂ))) := by ring
        _ = _ := by
          have hr : (scalar*(∑ r : Roots, (small r : ℂ)))*phase =
              ∑ r : Roots, scalar*(small r : ℂ)*phase := by rw [Finset.mul_sum,Finset.sum_mul]
          rw [hr,Finset.sum_mul]
          congr 1
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.mul_sum]
    · have hzero : giantTwoSidedIndependentResidueMean labels q offset = 0 := by
        unfold giantTwoSidedIndependentResidueMean
        simp only [giantTwoSidedIndependentResidueFactor_incompatible labels q offset hc,
          Finset.sum_const_zero,zero_div]
      have hv (r : Roots) : ¬ (raw r).valid κ := fun h => hc h.2.1
      simp only [hs,ite_true,hzero,Complex.ofReal_zero,mul_zero,zero_mul,hv,ite_false,Finset.sum_const_zero]
  · have hv (r : Roots) : ¬ (raw r).valid κ := fun h => hs h.1
    simp only [hs,hv,ite_false,Finset.sum_const_zero,mul_zero]

theorem giantSignedFixedPatternFourier_eq_lifespans (κ : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell) (θ : AddCircle (1 : ℝ))
    (hdis : Pairwise (fun g h : S ⊕ B => Disjoint (Bands g) (Bands h)))
    (hb : ∀ p : ↥(markedPhysicalBandPrimes PB),
      giantSignedPrimeResidueBaseline p.val (markedMemoryVisitQ q n) ≠ 0) :
    ((giantTwoSidedResidueSlotNormalization (J := S ⊕ B) (k+ell) : ℂ)^n)*
      (∑ slots : Slots, giantTwoSidedIndependentFourierMoment Pattern slots.1 slots.2.1 slots.2.2 κ q ζ
        (fun i => giantSignedJoinedCoefficient (PS := PS) (K i)) θ) =
      (fixedLifespanBaseline PB q n : ℂ)*
        ∑ path : GiantSignedLifespanOriginalPath PS PB (ell := ell) C κ,
          ∑ c : GiantSignedFixedLifespanChoices path (markedMemoryVisitQ q n),
            giantSignedFixedLifespanSourceWeight path q ζ K θ c := by
  letI := giantSignedLifespanRawPathFintype (PS := PS) (PB := PB) (ell := ell) (C := C)
  let f (raw : Raw) := fixedLifespanRawTerm raw κ q ζ K θ
  have hraw : (∑ slots : Slots, ∑ labels : Labels, ∑ r : Roots,
      if GiantSignedLifespanRawPath.valid (PS := PS) (PB := PB) (ell := ell) (C := C) ⟨slots,labels,r⟩ κ then f ⟨slots,labels,r⟩ else 0) =
        ∑ raw : Raw, if raw.valid κ then f raw else 0 := by
    simp only [Fintype.sum_prod_type]
  simp_rw [fixedLifespanSlots_sum (q := q) (ζ := ζ) (K := K) (θ := θ) (κ := κ) (hdis := hdis) (hb := hb)]
  rw [← Finset.mul_sum, mul_left_comm]
  congr 1
  rw [hraw,giantSignedLifespanOriginalPath_sum_guarded κ f,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro path _
  dsimp only [f,fixedLifespanRawTerm,giantSignedLifespanOriginalPathRawEquiv,Equiv.coe_fn_mk,
    GiantSignedLifespanRawPath.offset]
  rw [Finset.mul_sum]
  let Choices := GiantSignedFixedLifespanChoices path (markedMemoryVisitQ q n)
  apply Finset.sum_congr (congrArg (@Finset.univ Choices) (Subsingleton.elim _ _))
  intro c _
  simp only [giantSignedFixedLifespanSourceWeight,GiantSignedLifespanOriginalPath.offset,
    GiantSignedLifespanOriginalPath.increment,mul_assoc]

private def fixedPatternSlotsEquiv {I : Type*} (patterns : Fin n → Finset I)
    (C : Fin n → I → B → Finset (Fin k)) :
    ((i : Fin n) → GiantTwoSidedResidueEdgeChoice (P := Bands) (patterns i)
      (fun a => giantSignedJoinedPattern (C i a)) ell) ≃
      Σ p : (i : Fin n) → ↥(patterns i), GiantSignedLifespanPathSlots PS PB ell (fun i => C i (p i).val) where
  toFun x := ⟨fun i => (x i).1, (fun i => (x i).2.1), (fun i => (x i).2.2.1), (fun i => (x i).2.2.2)⟩
  invFun x i := ⟨x.1 i,x.2.1 i,x.2.2.1 i,x.2.2.2 i⟩
  left_inv x := by
    funext i
    change (⟨(x i).1,(x i).2.1,(x i).2.2.1,(x i).2.2.2⟩ :
      GiantTwoSidedResidueEdgeChoice (P := Bands) (patterns i)
        (fun a => giantSignedJoinedPattern (C i a)) ell) = x i
    rcases x i with ⟨a,π,τ,aux⟩
    rfl
  right_inv x := by rcases x with ⟨p,π,τ,aux⟩; rfl

theorem giantTwoSidedExpandedIndependentFourierMoment_eq_fixedLifespans {I : Type*}
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i a, GiantTwoSidedPatternCoefficient PB (C i a) ell) (θ : AddCircle (1 : ℝ))
    (hdis : Pairwise (fun g h : S ⊕ B => Disjoint (Bands g) (Bands h)))
    (hb : ∀ p : ↥(markedPhysicalBandPrimes PB),
      giantSignedPrimeResidueBaseline p.val (markedMemoryVisitQ q n) ≠ 0) :
    giantTwoSidedExpandedIndependentFourierMoment patterns (fun i a => giantSignedJoinedPattern (C i a))
      κ q ζ (fun i a => giantSignedJoinedCoefficient (PS := PS) (K i a)) θ =
      ((∏ p : ↥(markedPhysicalBandPrimes PB), giantSignedPrimeResidueBaseline p.val (markedMemoryVisitQ q n) : ℝ) : ℂ)*
        ∑ p : (i : Fin n) → ↥(patterns i),
          ∑ path : GiantSignedLifespanOriginalPath PS PB (ell := ell) (fun i => C i (p i).val) κ,
            ∑ c : GiantSignedFixedLifespanChoices path (markedMemoryVisitQ q n),
              giantSignedFixedLifespanSourceWeight path q ζ (fun i => K i (p i).val) θ c := by
  let Choice (i : Fin n) := GiantTwoSidedResidueEdgeChoice (P := Bands) (patterns i)
    (fun a => giantSignedJoinedPattern (C i a)) ell
  let f (x : (i : Fin n) → Choice i) := giantTwoSidedIndependentFourierMoment
    (fun i => giantSignedJoinedPattern (C i (x i).1.val)) (fun i => (x i).2.1) (fun i => (x i).2.2.1)
    (fun i => (x i).2.2.2) κ q ζ (fun i => giantSignedJoinedCoefficient (PS := PS) (K i (x i).1.val)) θ
  let PatternPath := (i : Fin n) → ↥(patterns i)
  letI (p : PatternPath) : Fintype (GiantSignedLifespanPathSlots PS PB ell (fun i => C i (p i).val)) :=
    let perms : Fintype (Fin n → S ⊕ B → Equiv.Perm (Fin (k+ell))) := inferInstance
    let aux : Fintype ((i : Fin n) → GiantTwoSidedPatternAuxiliary Bands
      (giantSignedJoinedPattern (C i (p i).val))) := inferInstance
    @instFintypeProd _ _ perms (@instFintypeProd _ _ perms aux)
  let e := fixedPatternSlotsEquiv (PS := PS) (PB := PB) (ell := ell) patterns C
  change ((giantTwoSidedResidueSlotNormalization (J := S ⊕ B) (k+ell) : ℂ)^n)*(∑ x, f x) = _
  rw [← e.symm.sum_comp f,Fintype.sum_sigma,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact giantSignedFixedPatternFourier_eq_lifespans κ q ζ (fun i => K i (p i).val) θ hdis hb

end
end ArtinMatthews

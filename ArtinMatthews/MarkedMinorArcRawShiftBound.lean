module

public import ArtinMatthews.MarkedMinorArcRawShiftTransport


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine actual-state shifted-cell-union operator estimate. It uses
the actual first-good physical projection, all indexed pending particles,
the literal tilted prime atoms, and the proved product-variable transport. -/
namespace ArtinMatthews
open Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator

/-- Enlarge only the literal ratio width in already derived cell geometry. -/
theorem markedMinorCleanCellGeometry_mono_width {r Y c L R T : ℝ}
    (d : MarkedMinorCleanCellData) (h : MarkedMinorCleanCellGeometry r Y c L R d)
    (hY : 0 ≤ Y) (hRT : R ≤ T) : MarkedMinorCleanCellGeometry r Y c L T d := by
  obtain ⟨hD,hDsq,hd,hg,hzlo,hzhi,hτ,hlines,hcell⟩ := h
  refine ⟨hD,hDsq,hd,hg,hzlo,hzhi,hτ,hlines,?_⟩
  intro v hv
  exact (hcell v hv).trans (by gcongr)

set_option maxHeartbeats 1500000 in
/-- Genuine raw-state clean bound on every actual shifted two-cell union
that has a surviving first-good source. The threshold is uniform in every
active and pending size, copied background, root line and cell index. Its
major-arc exponent G+4 is independent of all band exponents. -/
theorem marked_minor_actual_raw_shift_union_opNorm {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ t, ‖η t‖ ≤ 1)
    {G H c L : ℝ} (hG : 0 < G) (hH : 1 ≤ H) (hc : 0 < c) (hL : 0 ≤ L) (N : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (q r d₀ Y ρ : ℝ)
      (w : Z → ℤ × ℤ) (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (bg : MarkedRawBackground (markedRawActualPrimeBand e x) pads B)
      (u v : MarkedRawCleanFiber (markedRawActualPrimeBand e x) Z) (shift : ℤ),
      0 ≤ q → q ≤ 1 → 0 < d₀ → 0 ≤ ρ → ρ ≤ 1 →
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5:ℝ)) →
      (∀ z, markedMinorIntegerDet z.1 (w z)=1) →
      (∀ z ∈ Z, c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ L) →
      (∀ s, ‖χ s‖ ≤ 1) → |shift| ≤ (N : ℤ) →
      markedRawCleanKernel hZ ψ η d₀ Y ((Real.log x)^(G+4)) ρ
        (markedRawFirstGoodCutoff r d₀ Y w χ) bg u v ≠ 0 →
      ‖markedRawShiftCountingMatrix (markedRawActualPrimeAtom e q x) hZ ψ η r d₀ Y
        ((Real.log x)^(G+4)) ρ (markedRawFirstGoodCutoff r d₀ Y w χ) bg u.1 shift‖ ≤
        (Real.log x)^(-G) := by
  classical
  have hR : 0 ≤ (N : ℝ)+1 := by positivity
  filter_upwards [markedRawShiftCountingMatrix_transport_eventually e hinj,
    markedRawActualProductMap_injective_eventually e hinj,
    markedRawActualPrimeBand_disjoint_eventually e hinj,
    marked_minor_actual_memory_clean_opNorm e he hinj ψ η hη hηnorm hG hH hc hL hR]
    with x htransport hinject hdis hclean
  intro pads B Z hZ q r d₀ Y ρ w χ bg u v shift hq₀ hq₁ hd₀ hρ₀ hρ₁ hYlo hYhi hw hτ hχ hshift hnonzero
  have hY : 0 < Y := (Real.exp_pos _).trans_le hYlo
  have hsupport := markedRawCleanKernel_ne_zero_support hZ ψ η d₀ Y _ ρ _ bg u v hnonzero
  have hDsq := markedRawCleanKernel_ne_zero_squarefree hdis hZ ψ η d₀ Y _ ρ _ bg u v hnonzero
  have hD : (0 : ℝ) < markedRawCopiedProduct bg.1 := by exact_mod_cast markedRawCopiedProduct_pos bg.1
  have hgeo := markedRawCleanShiftCellGeometry hdis hZ ψ η r hd₀ hY w hw hτ _ ρ χ bg u v shift hnonzero
  have hshiftR : ((|shift| : ℤ) : ℝ)+1 ≤ (N : ℝ)+1 := by
    have hh : ((|shift| : ℤ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hshift
    linarith
  have hgeo' := markedMinorCleanCellGeometry_mono_width _ hgeo hY.le hshiftR
  obtain ⟨hDnat,hDsq',hd,hg,hzlo,hzhi,hτ',hlines,hcell⟩ := hgeo'
  have hbase := hclean q Y r _ _ (markedRawProductSupport (markedRawActualPrimeBand e x)) _ _ hq₀ hq₁ hYlo hYhi hDnat hDsq' hd hg hzlo hzhi hτ' hlines hcell
  rw [htransport pads B Z hZ ψ η w q r d₀ Y _ ρ _ bg u.1 shift hY hDsq hsupport.1]
  let Positions := markedRawShiftPositionSet hZ r d₀ Y (markedRawCopiedProduct bg.1) u.1 shift
  let Products := markedRawProductSupport (markedRawActualPrimeBand e x)
  let A : Matrix (Positions × Products) (Positions × Products) ℂ :=
    markedWeightedCountingMatrix (fun i => markedMinorIntegerProductMass e q x i.2.1)
      (markedMinorActualCleanRawMatrix ψ η (markedRawCopiedProduct bg.1) Y ((Real.log x)^(G+4)) Positions Products)
  let ep : MarkedRawCleanFiber (markedRawActualPrimeBand e x) Positions → ℂ := fun a =>
    markedRawEndpointFactor hZ ρ (markedRawFirstGoodCutoff r d₀ Y w χ)
      ((markedRawStateSplit pads B Z).symm
        (bg,markedRawShiftFiberInclude hZ r d₀ Y (markedRawCopiedProduct bg.1) u.1 shift a))
  change ‖((d₀/(markedRawCopiedProduct bg.1 : ℝ) : ℝ) : ℂ) •
    markedMinorEndpointMatrix (A.submatrix markedRawProductMap markedRawProductMap) ep ep‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (div_nonneg hd₀.le hD.le)]
  have hep := markedMinorEndpointMatrix_norm_le
    (A.submatrix markedRawProductMap markedRawProductMap) ep ep
    (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)≤1)
    (fun a => markedRawEndpointFactor_norm_le hZ hρ₀ hρ₁ _
      (markedRawFirstGoodCutoff_norm_le r d₀ Y w χ hχ) _)
    (fun a => markedRawEndpointFactor_norm_le hZ hρ₀ hρ₁ _
      (markedRawFirstGoodCutoff_norm_le r d₀ Y w χ hχ) _)
  simp only [one_mul] at hep
  have hsub := markedMinorSubmatrix_injective_norm_le A markedRawProductMap (hinject _)
  have hratio : d₀/(markedRawCopiedProduct bg.1 : ℝ) ≤ 1 := (div_le_one hD).mpr hsupport.1.1
  calc
    _ ≤ (d₀/(markedRawCopiedProduct bg.1 : ℝ))*‖A‖ :=
      mul_le_mul_of_nonneg_left (hep.trans hsub) (div_nonneg hd₀.le hD.le)
    _ ≤ ‖A‖ := mul_le_of_le_one_left (norm_nonneg _) hratio
    _ ≤ _ := hbase

end ArtinMatthews

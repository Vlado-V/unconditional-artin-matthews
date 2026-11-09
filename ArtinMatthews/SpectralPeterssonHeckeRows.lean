module

public import ArtinMatthews.SpectralPeterssonHeckeAction
public import ArtinMatthews.SpectralPeterssonHeckeOrbital
public import ArtinMatthews.SpectralPeterssonRowSectors


set_option backward.privateInPublic true
@[expose] public section

/-! The positive-regulator series agrees with the genuine grouping by
positive moduli. At zero the grouped formula is the limit candidate. -/

noncomputable section
open Set Matrix UpperHalfPlane
open scoped MatrixGroups

namespace ArtinMatthews

def gamma0PeterssonHeckeZeroSector (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (u : ℝ) (m : ℕ+) (z : UpperHalfPlane) : ℂ :=
  ∑' p : Gamma0PeterssonZeroRow N b a, gamma0PeterssonHeckeSignedSummand N b a u m p.val.val z

def gamma0PeterssonHeckeGrouped (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (u : ℝ) (m : ℕ+) (z : UpperHalfPlane) : ℂ :=
  gamma0PeterssonHeckeZeroSector N b a u m z+∑' c, gamma0PeterssonHeckeModulus N b a u m c z

theorem gamma0PeterssonHeckeNonzeroRowExpand_summand (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (u : ℝ) (m : ℕ+) (c : Ioi (0 : ℕ)) (R : gamma0TrueWidthReducedMatrix N b a c.val) (l : ℤ) :
    gamma0PeterssonHeckeSignedSummand N b a u m (gamma0PeterssonNonzeroRowExpand N b a ⟨c,R,l⟩).val.val =
      spectralHolomorphicSlash 2 (gamma0TrueWidthMatrix N b a R.val*realTranslation (l : ℝ))
        (spectralPeterssonHeckeSeed u m) := by
  let M := gamma0TrueWidthDoubleCosetExpand N b a c.val (R,0,l)
  change gamma0PeterssonHeckeSignedSummand N b a u m
    (gamma0PeterssonRowOfMatrix N b a ⟨M.val,M.property.1⟩) = _
  rw [gamma0PeterssonHeckeSignedSummand_of_matrix]
  unfold gamma0PeterssonHeckeMatrixSeed
  have h : gamma0TrueWidthMatrix N b a M.val = gamma0TrueWidthMatrix N b a R.val*realTranslation (l : ℝ) := by
    change gamma0TrueWidthMatrix N b a
      (integerTranslation ((gamma0CuspTrueWidth N a : ℤ)*0)*R.val*
        integerTranslation ((gamma0CuspTrueWidth N b : ℤ)*l)) = _
    simpa only [Int.cast_zero,realTranslation_zero,one_mul] using
      gamma0Petersson_normalized_translate N b a R.val 0 l
  rw [h]

theorem gamma0PeterssonHeckeChart_eq_grouped (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (u : ℝ) (hu : 0 < u) (m : ℕ+) (z : UpperHalfPlane) :
    gamma0PeterssonHeckeChart N b a u m z = gamma0PeterssonHeckeGrouped N b a u m z := by
  let f (p : Gamma0PeterssonPositiveRow N b a) := gamma0PeterssonHeckeSignedSummand N b a u m p.val z
  let S : Set (Gamma0PeterssonPositiveRow N b a) := {p | p.val.val 0=0}
  let e := gamma0PeterssonNonzeroRowEquiv N b a
  let g (p : Σ c : Ioi (0 : ℕ), gamma0TrueWidthReducedMatrix N b a c.val × ℤ) := f (e p).val
  have hs : Summable f := ((gamma0PeterssonHeckeSignedSummand_summable N b a u hu m z).subtype
    {p | gamma0PeterssonRowPositive p}).of_norm
  have hg : Summable g := (hs.subtype (Sᶜ)).comp_injective e.injective
  have hmod (c : Ioi (0 : ℕ)) : (∑' p : gamma0TrueWidthReducedMatrix N b a c.val × ℤ, g ⟨c,p⟩) =
      gamma0PeterssonHeckeModulus N b a u m c z := by
    let _ : NeZero c.val := ⟨c.property.ne'⟩
    calc
      _ = ∑' R : gamma0TrueWidthReducedMatrix N b a c.val, ∑' l : ℤ, g ⟨c,R,l⟩ := (hg.sigma_factor c).tsum_prod
      _ = ∑' R : gamma0TrueWidthReducedMatrix N b a c.val,
          spectralPeterssonHeckeOrbital u m (gamma0TrueWidthMatrix N b a R.val) z := by
        apply tsum_congr
        intro R
        unfold spectralPeterssonHeckeOrbital
        exact tsum_congr (fun l => congrFun (gamma0PeterssonHeckeNonzeroRowExpand_summand N b a u m c R l) z)
      _ = _ := by rw [tsum_fintype]; rfl
  rw [gamma0PeterssonHeckeChart_eq_positive N b a u hu m z]
  change (∑' p, f p) = (∑' p : ↥S, f p.val)+∑' c, gamma0PeterssonHeckeModulus N b a u m c z
  rw [← hs.tsum_subtype_add_tsum_subtype_compl S]
  congr 1
  calc
    _ = ∑' p, g p := (e.tsum_eq (fun p => f p.val)).symm
    _ = ∑' c, ∑' p : gamma0TrueWidthReducedMatrix N b a c.val × ℤ, g ⟨c,p⟩ := hg.tsum_sigma
    _ = _ := tsum_congr hmod

theorem gamma0PeterssonHeckeZeroSector_of_inequivalent (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (h : ¬ gamma0EisensteinCuspsEquivalent N b a) (u : ℝ) (m : ℕ+) (z : UpperHalfPlane) :
    gamma0PeterssonHeckeZeroSector N b a u m z = 0 := by
  let _ := gamma0PeterssonZeroRow_isEmpty_of_inequivalent N b a h
  simp only [gamma0PeterssonHeckeZeroSector,tsum_empty]

theorem gamma0PeterssonHeckeZeroSector_same_chart (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (u : ℝ) (m : ℕ+) (z : UpperHalfPlane) :
    gamma0PeterssonHeckeZeroSector N a a u m z = spectralPeterssonHeckeSeed u m z := by
  unfold gamma0PeterssonHeckeZeroSector
  rw [tsum_eq_single (gamma0PeterssonZeroRow_identity N a) (fun p hp => (hp (Subsingleton.elim p _)).elim)]
  let M : gamma0CuspCorrespondence N a a := ⟨1,by
    change a⁻¹*1*a ∈ CongruenceSubgroup.Gamma0 N
    simp⟩
  change gamma0PeterssonHeckeSignedSummand N a a u m (gamma0PeterssonRowOfMatrix N a a M) z = _
  rw [gamma0PeterssonHeckeSignedSummand_of_matrix]
  have hM : gamma0TrueWidthMatrix N a a M.val = 1 := by
    unfold gamma0TrueWidthMatrix
    change (gamma0PeterssonWidthDilation N a)⁻¹*atkinRealMap 1*gamma0PeterssonWidthDilation N a = 1
    simp only [map_one,mul_one,inv_mul_cancel]
  rw [gamma0PeterssonHeckeMatrixSeed,hM,spectralHolomorphicSlash,map_one,SlashAction.slash_one]

end ArtinMatthews

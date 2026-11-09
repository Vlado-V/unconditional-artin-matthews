module

public import ArtinMatthews.SpectralPeterssonFourierRows
public import ArtinMatthews.SpectralPeterssonRowSectors
public import ArtinMatthews.SpectralPeterssonWeylOrbital
public import ArtinMatthews.SpectralTrueWidthKloosterman


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Poincare Fourier coefficient at the true-width cusp is the
zero sector plus the genuine Kloosterman–Bessel series. -/

noncomputable section
open Set UpperHalfPlane Matrix
open scoped MatrixGroups ModularForm

namespace ArtinMatthews

theorem spectralPeterssonWeylOrbital_fourier (k : ℕ) (hk : 2 ≤ k) (m n : ℕ+)
    (G : SL(2, ℝ)) (hC : 0 < G 1 0) (y : ℝ) (hy : 0 < y) :
    spectralPeterssonFourierAtHeight (fun z => ∑' l : ℤ, spectralHolomorphicSlash k
      (G*realTranslation (l : ℝ)) (spectralHolomorphicCuspSeed (m : ℕ)) z) n y hy =
      spectralPeterssonWeylOrbitalCoefficient k m n G := by
  apply spectralPeterssonFourierAtHeight_qExpansion
  · exact (spectralPeterssonWeylOrbital_qExpansion k hk m G hC
      (spectralPeterssonHeightPoint 0 y hy)).1
  · intro x _
    exact (spectralPeterssonWeylOrbital_qExpansion k hk m G hC
      (spectralPeterssonHeightPoint x y hy)).2

theorem gamma0PeterssonNonzeroRowExpand_summand (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (m : ℕ+) (c : Ioi (0 : ℕ)) (R : gamma0TrueWidthReducedMatrix N b a c.val) (l : ℤ) :
    gamma0PeterssonSignedSummand N b a k (m : ℕ)
      (gamma0PeterssonNonzeroRowExpand N b a ⟨c,R,l⟩).val.val =
      spectralHolomorphicSlash k (gamma0TrueWidthMatrix N b a R.val*realTranslation (l : ℝ))
        (spectralHolomorphicCuspSeed (m : ℕ)) := by
  let M := gamma0TrueWidthDoubleCosetExpand N b a c.val (R,0,l)
  change gamma0PeterssonSignedSummand N b a k (m : ℕ)
    (gamma0PeterssonRowOfMatrix N b a ⟨M.val,M.property.1⟩) = _
  rw [gamma0PeterssonSignedSummand_of_matrix]
  unfold gamma0PeterssonMatrixSeed
  have h : gamma0TrueWidthMatrix N b a M.val =
      gamma0TrueWidthMatrix N b a R.val*realTranslation (l : ℝ) := by
    change gamma0TrueWidthMatrix N b a
      (integerTranslation ((gamma0CuspTrueWidth N a : ℤ)*0)*R.val*
        integerTranslation ((gamma0CuspTrueWidth N b : ℤ)*l)) = _
    simpa only [Int.cast_zero,realTranslation_zero,one_mul] using
      gamma0Petersson_normalized_translate N b a R.val 0 l
  rw [h]

theorem gamma0PeterssonFourierAtHeight_orbit (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (hk : 3 ≤ k) (m n : ℕ+) (c : Ioi (0 : ℕ))
    (R : gamma0TrueWidthReducedMatrix N b a c.val) (y : ℝ) (hy : 0 < y) :
    (∑' l : ℤ, spectralPeterssonFourierAtHeight
      (gamma0PeterssonSignedSummand N b a k (m : ℕ)
        (gamma0PeterssonNonzeroRowExpand N b a ⟨c,R,l⟩).val.val) n y hy) =
      spectralPeterssonWeylOrbitalCoefficient k m n (gamma0TrueWidthMatrix N b a R.val) := by
  let g (l : ℤ) := (gamma0PeterssonNonzeroRowExpand N b a ⟨c,R,l⟩).val
  let F (l : ℤ) := gamma0PeterssonSignedSummand N b a k (m : ℕ) (g l).val
  have hg : Function.Injective g := by
    intro l l' h
    exact congrArg (fun q : Σ c : Ioi (0 : ℕ), gamma0TrueWidthReducedMatrix N b a c.val × ℤ => q.2.2)
      ((gamma0PeterssonNonzeroRowExpand_bijective N b a).1 (Subtype.ext h))
  obtain ⟨u,hu,hbound⟩ := gamma0PeterssonHorizontalRow_majorant N b a k hk m y hy
  obtain ⟨_,hCoeff⟩ := spectralPeterssonFourierAtHeight_tsum F n y hy (u ∘ g)
    (hu.comp_injective hg) (fun l => gamma0PeterssonSignedSummand_continuous N b a k (m : ℕ) (g l).val)
    (fun l x hx => hbound (g l) x hx)
  have hC : 0 < gamma0TrueWidthMatrix N b a R.val 1 0 := by
    rw [gamma0TrueWidthMatrix_lower N b a R.val (c.val : ℤ) R.property.2.1]
    exact gamma0TrueWidthModulus_pos N b a (Nat.cast_pos.mpr c.property)
  change (∑' l, spectralPeterssonFourierAtHeight (F l) n y hy) = _
  rw [← hCoeff]
  have hF : (fun z => ∑' l, F l z) =
      fun z => ∑' l : ℤ, spectralHolomorphicSlash k
        (gamma0TrueWidthMatrix N b a R.val*realTranslation (l : ℝ)) (spectralHolomorphicCuspSeed (m : ℕ)) z := by
    funext z
    exact tsum_congr (fun l => congrFun (gamma0PeterssonNonzeroRowExpand_summand N b a k m c R l) z)
  rw [hF]
  exact spectralPeterssonWeylOrbital_fourier k (by omega) m n _ hC y hy

def gamma0PeterssonPositiveModulusTerm (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (m n : ℕ+) (c : Ioi (0 : ℕ)) : ℂ :=
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  let C := gamma0TrueWidthModulus N b a (c.val : ℝ)
  gamma0TrueWidthKloostermanSum N b a c.val (n : ℤ) (m : ℤ)*
    (2*(Real.pi : ℂ)*Complex.I^(-(k : ℤ))/(C : ℂ))*
    ((Real.sqrt ((n : ℝ)/(m : ℝ)) : ℝ) : ℂ)^(k-1)*
    Complex.besselJ ((k-1 : ℕ) : ℂ) (spectralPeterssonBesselArgument m n C : ℂ)

theorem gamma0PeterssonWeylOrbitalCoefficient_sum (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (m n : ℕ+) (c : Ioi (0 : ℕ)) :
    let _ : NeZero c.val := ⟨c.property.ne'⟩
    (∑ R : gamma0TrueWidthReducedMatrix N b a c.val,
      spectralPeterssonWeylOrbitalCoefficient k m n (gamma0TrueWidthMatrix N b a R.val)) =
      gamma0PeterssonPositiveModulusTerm N b a k m n c := by
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  dsimp only [gamma0PeterssonPositiveModulusTerm]
  rw [gamma0TrueWidthKloostermanSum_normalized,Finset.sum_mul,Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro R _
  unfold spectralPeterssonWeylOrbitalCoefficient
  rw [gamma0TrueWidthMatrix_lower N b a R.val (c.val : ℤ) R.property.2.1]
  push_cast
  ring

def gamma0PeterssonZeroFourierTerm (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (m n : ℕ+) (y : ℝ) (hy : 0 < y) : ℂ :=
  ∑' p : Gamma0PeterssonZeroRow N b a, spectralPeterssonFourierAtHeight
    (gamma0PeterssonSignedSummand N b a k (m : ℕ) p.val.val) n y hy

theorem gamma0PeterssonZeroFourierTerm_of_inequivalent (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (h : ¬ gamma0EisensteinCuspsEquivalent N b a) (k : ℕ) (m n : ℕ+) (y : ℝ) (hy : 0 < y) :
    gamma0PeterssonZeroFourierTerm N b a k m n y hy = 0 := by
  let _ := gamma0PeterssonZeroRow_isEmpty_of_inequivalent N b a h
  simp only [gamma0PeterssonZeroFourierTerm,tsum_empty]

theorem gamma0PeterssonZeroFourierTerm_same_chart (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (m n : ℕ+) (y : ℝ) (hy : 0 < y) :
    gamma0PeterssonZeroFourierTerm N a a k m n y hy = if m = n then 1 else 0 := by
  unfold gamma0PeterssonZeroFourierTerm
  rw [tsum_eq_single (gamma0PeterssonZeroRow_identity N a) (fun p hp => (hp (Subsingleton.elim p _)).elim)]
  let M : gamma0CuspCorrespondence N a a := ⟨1,by
    change a⁻¹*1*a ∈ CongruenceSubgroup.Gamma0 N
    simp⟩
  change spectralPeterssonFourierAtHeight (gamma0PeterssonSignedSummand N a a k (m : ℕ)
    (gamma0PeterssonRowOfMatrix N a a M)) n y hy = _
  rw [gamma0PeterssonSignedSummand_of_matrix]
  have hM : gamma0TrueWidthMatrix N a a M.val = 1 := by
    unfold gamma0TrueWidthMatrix
    change (gamma0PeterssonWidthDilation N a)⁻¹*atkinRealMap 1*gamma0PeterssonWidthDilation N a = 1
    simp only [map_one,mul_one,inv_mul_cancel]
  have hseed : spectralHolomorphicCuspSeed (m : ℕ) = fun z => spectralPeterssonQ z^(m : ℕ) := by
    funext z
    rw [spectralHolomorphicCuspSeed,spectralPeterssonQ,← Complex.exp_nat_mul]
    congr 1
    ring
  unfold gamma0PeterssonMatrixSeed
  rw [hM,spectralHolomorphicSlash,map_one,SlashAction.slash_one,hseed,spectralPeterssonFourierAtHeight_mode]

theorem gamma0PeterssonFourierAtHeight_geometric (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (hk : 3 ≤ k) (m n : ℕ+) (y : ℝ) (hy : 0 < y) :
    Summable (gamma0PeterssonPositiveModulusTerm N b a k m n) ∧
      spectralPeterssonFourierAtHeight (gamma0PeterssonPoincareChart N b a k (m : ℕ)) n y hy =
        gamma0PeterssonZeroFourierTerm N b a k m n y hy +
          ∑' c, gamma0PeterssonPositiveModulusTerm N b a k m n c := by
  let f (p : Gamma0PeterssonPositiveRow N b a) := spectralPeterssonFourierAtHeight
    (gamma0PeterssonSignedSummand N b a k (m : ℕ) p.val) n y hy
  let S : Set (Gamma0PeterssonPositiveRow N b a) := {p | p.val.val 0 = 0}
  let e := gamma0PeterssonNonzeroRowEquiv N b a
  let g (p : Σ c : Ioi (0 : ℕ), gamma0TrueWidthReducedMatrix N b a c.val × ℤ) := f (e p).val
  obtain ⟨hs,hf⟩ := gamma0PeterssonFourierAtHeight_rows N b a k hk m n y hy
  have hg : Summable g := (hs.subtype (Sᶜ)).comp_injective e.injective
  have hmod (c : Ioi (0 : ℕ)) : (∑' p : gamma0TrueWidthReducedMatrix N b a c.val × ℤ, g ⟨c,p⟩) =
      gamma0PeterssonPositiveModulusTerm N b a k m n c := by
    let _ : NeZero c.val := ⟨c.property.ne'⟩
    calc
      _ = ∑' R : gamma0TrueWidthReducedMatrix N b a c.val, ∑' l : ℤ, g ⟨c,R,l⟩ :=
        (hg.sigma_factor c).tsum_prod
      _ = ∑' R : gamma0TrueWidthReducedMatrix N b a c.val,
          spectralPeterssonWeylOrbitalCoefficient k m n (gamma0TrueWidthMatrix N b a R.val) :=
        tsum_congr (fun R => gamma0PeterssonFourierAtHeight_orbit N b a k hk m n c R y hy)
      _ = _ := by rw [tsum_fintype]; exact gamma0PeterssonWeylOrbitalCoefficient_sum N b a k m n c
  refine ⟨hg.sigma.congr hmod,?_⟩
  rw [hf]
  change (∑' p, f p) = (∑' p : ↥S, f p.val)+∑' c, gamma0PeterssonPositiveModulusTerm N b a k m n c
  rw [← hs.tsum_subtype_add_tsum_subtype_compl S]
  congr 1
  calc
    _ = ∑' p, g p := (e.tsum_eq (fun p => f p.val)).symm
    _ = ∑' c, ∑' p : gamma0TrueWidthReducedMatrix N b a c.val × ℤ, g ⟨c,p⟩ := hg.tsum_sigma
    _ = _ := tsum_congr hmod

end ArtinMatthews

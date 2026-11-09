module

public import ArtinMatthews.MarkedMinorArcDirtyMajorLine
public import ArtinMatthews.MarkedMinorArcDirtyMajorCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine promoted-anchor target counts on the actual good shared lattice.
The source determinant cutoff directly puts every target in one shear box. -/
namespace ArtinMatthews
open Finset
noncomputable section

 theorem markedDirtyMajor_box_area_bound {Y C : ℝ} (hY : 0 < Y) (_hC : 0 ≤ C)
    (M N p : ℕ) (hp : 0 < p)
    (hM : Y^(1/10:ℝ) ≤ (M:ℝ)) (hN : Y^(1/10:ℝ) ≤ (N:ℝ))
    (hMN : (M:ℝ)*N ≤ C*Y) :
    (M:ℝ)*N/p+max (M:ℝ) N ≤ C*Y*(1/(p:ℝ)+Y^(-1/10:ℝ)) := by
  have hs : 0 < Y^(1/10:ℝ) := Real.rpow_pos_of_pos hY _
  have hmax : max (M:ℝ) N ≤ C*Y/(Y^(1/10:ℝ)) := by
    apply max_le
    · apply (le_div_iff₀ hs).mpr
      exact (mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg M)).trans hMN
    · apply (le_div_iff₀ hs).mpr
      have hh := mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg N)
      nlinarith
  calc
    _ ≤ C*Y/p+C*Y/(Y^(1/10:ℝ)) := add_le_add
      (div_le_div_of_nonneg_right hMN (by exact_mod_cast hp.le)) hmax
    _ = _ := by
      rw [show (-1/10:ℝ)=-(1/10:ℝ) by ring, Real.rpow_neg hY.le]
      ring

 theorem markedDirtyMajor_shared_box_count {P : Finset Nat.Primes}
    (particle : MarkedRawParticle P) (V : Finset (ℤ × ℤ))
    (hV : ∀ v ∈ V, IsCoprime v.1 v.2) {D : ℕ} (hD : 0 < D)
    (z w : ℤ × ℤ) (hd : markedMinorIntegerDet z w=1)
    (h l a b lo hi : ℤ) (hb : h*b-l*a=1) (M N : ℕ)
    (hpD : ¬((particle.1.1:ℕ):ℤ) ∣ (D:ℤ))
    (hdiv : ∀ v ∈ V,(D:ℤ) ∣ markedMinorIntegerDet z v)
    (hbox : ∀ v ∈ V, markedDirtyMajorReducedCoordinates D z w h l a b v ∈ markedMinorBox lo hi M N)
    (hhits : ∀ v (hv : v ∈ V), MarkedRawParticleHits P v (hV v hv) particle) :
    (V.card:ℝ) ≤ (M:ℝ)*N/(particle.1.1:ℕ)+max (M:ℝ) N := by
  apply markedDirtyMajor_particle_targets_count particle V hV
    (markedDirtyMajorLatticeVector D z w (h,l)) (markedDirtyMajorLatticeVector D z w (a,b))
    (by rwa [markedDirtyMajor_lattice_basis_det D z w hd h l a b hb])
    (markedDirtyMajorReducedCoordinates D z w h l a b)
    (markedDirtyMajor_reduced_injective hD.ne' z w hd h l a b hb V hdiv)
    (fun v hv => markedDirtyMajor_reduced_decompose hD.ne' z w v hd h l a b hb (hdiv v hv))
    lo hi M N hbox hhits

 /-- No counting or distribution hypothesis occurs: the actual primitive
particle anchor and actual good shear supply the complete line count. -/
 theorem markedDirtyMajor_good_shared_count {P : Finset Nat.Primes}
    (particle : MarkedRawParticle P) (V : Finset (ℤ × ℤ))
    (hV : ∀ v ∈ V, IsCoprime v.1 v.2) {D : ℕ} (hD : 0 < D)
    (z w : ℤ × ℤ) (hd : markedMinorIntegerDet z w=1)
    (r : ℝ) {Y C : ℝ} (hY : 1 ≤ Y) (hC : 1 ≤ C)
    (hg : MarkedMinorShearGood ((D:ℝ)*markedMinorIntegerTau r w/markedMinorIntegerTau r z) Y)
    (hpD : ¬((particle.1.1:ℕ):ℤ) ∣ (D:ℤ))
    (hdiv : ∀ v ∈ V,(D:ℤ) ∣ markedMinorIntegerDet z v)
    (hpoints : ∀ v ∈ V,
      |((markedMinorSharedCoordinates D z w v).1:ℝ)+((markedMinorSharedCoordinates D z w v).2:ℝ)*
        ((D:ℝ)*markedMinorIntegerTau r w/markedMinorIntegerTau r z)| ≤ C ∧
      |((markedMinorSharedCoordinates D z w v).2:ℝ)/Y| ≤ C)
    (hhits : ∀ v (hv : v ∈ V), MarkedRawParticleHits P v (hV v hv) particle) :
    (V.card:ℝ) ≤ (300*C^2)*Y*(1/(particle.1.1:ℕ)+Y^(-1/10:ℝ)) := by
  obtain ⟨h,l,a,b,lo,hi,M,N,hb,hM,hN,hMN,_hMhi,_hNhi,hcover⟩ :=
    markedMinorShear_good_integer_box _ hY hC hg
  have hc := markedDirtyMajor_shared_box_count particle V hV hD z w hd h l a b lo hi hb M N
    hpD hdiv (fun v hv => hcover _ (hpoints v hv).1 (hpoints v hv).2) hhits
  exact hc.trans (markedDirtyMajor_box_area_bound (by linarith) (by positivity) M N _
    particle.1.1.2.pos hM hN hMN)

 /-- Literal determinant-cutoff support and the physical tau box imply the
sheared box conditions; no neighboring-cell support is assumed. -/
 theorem markedDirtyMajor_cutoff_points (r : ℝ) {Y c B K : ℝ}
    (_hY : 0 < Y) (hc : 0 < c) (hB : 0 ≤ B) {D : ℕ} (hD : 0 < D)
    (z w : ℤ × ℤ) (hd : markedMinorIntegerDet z w=1)
    (hz : c ≤ |markedMinorIntegerTau r z|) (V : Finset (ℤ × ℤ))
    (hτ : ∀ v ∈ V, |markedMinorIntegerTau r v| ≤ B)
    (hdiv : ∀ v ∈ V,(D:ℤ) ∣ markedMinorIntegerDet z v)
    (hcut : ∀ v ∈ V, |(((markedMinorIntegerDet z v/(D:ℤ):ℤ):ℝ))/Y| ≤ K) :
    ∀ v ∈ V,
      |((markedMinorSharedCoordinates D z w v).1:ℝ)+((markedMinorSharedCoordinates D z w v).2:ℝ)*
        ((D:ℝ)*markedMinorIntegerTau r w/markedMinorIntegerTau r z)| ≤ max 1 (max (B/c) K) ∧
      |((markedMinorSharedCoordinates D z w v).2:ℝ)/Y| ≤ max 1 (max (B/c) K) := by
  intro v hv
  have hz0 : markedMinorIntegerTau r z ≠ 0 := abs_pos.mp (hc.trans_le hz)
  have hrep := markedMinorSharedCoordinates_decompose hD.ne' z w v hd (hdiv v hv)
  constructor
  · rw [markedMinorSharedLattice_shear r D z w v _ _ hrep.1 hrep.2 hz0,abs_div]
    exact ((div_le_div_of_nonneg_right (hτ v hv) (abs_nonneg _)).trans
      (div_le_div_of_nonneg_left hB hc hz)).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hcut v hv).trans ((le_max_right _ _).trans (le_max_right _ _))

end
end ArtinMatthews

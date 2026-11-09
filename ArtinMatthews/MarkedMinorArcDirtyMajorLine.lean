module

public import ArtinMatthews.MarkedMinorArcDirtyMajorCongruence
public import ArtinMatthews.MarkedMinorArcDirtyRawAnchor


set_option backward.privateInPublic true
@[expose] public section

/-! A genuinely promoted old particle supplies a nonzero homogeneous
congruence in any integer basis whose determinant is prime to its prime.
The target count includes all nonprimitive vectors in the comparison box. -/
namespace ArtinMatthews
open Finset
noncomputable section

-- Use the canonical additive structure of ZMod throughout field arithmetic.

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
 theorem markedDirtyMajor_line_coefficients {p : ℕ} (hp : p.Prime)
    (v E F : ℤ × ℤ) (hv : IsCoprime v.1 v.2)
    (hD : ¬(p:ℤ) ∣ markedMinorIntegerDet E F) :
    (markedMinorIntegerDet v E:ZMod p) ≠ 0 ∨ (markedMinorIntegerDet v F:ZMod p) ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  by_contra hn
  push Not at hn
  have hD' : (markedMinorIntegerDet E F:ZMod p) ≠ 0 :=
    fun hz => hD ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
  have h₁ : (v.1:ZMod p)*(markedMinorIntegerDet E F:ZMod p)=0 := by
    have ha := hn.1
    have hb := hn.2
    unfold markedMinorIntegerDet at *
    push_cast at *
    linear_combination (E.1:ZMod p)*hb-(F.1:ZMod p)*ha
  have h₂ : (v.2:ZMod p)*(markedMinorIntegerDet E F:ZMod p)=0 := by
    have ha := hn.1
    have hb := hn.2
    unfold markedMinorIntegerDet at *
    push_cast at *
    linear_combination (E.2:ZMod p)*hb-(F.2:ZMod p)*ha
  have hv₁ : (v.1:ZMod p)=0 := (mul_eq_zero.mp h₁).resolve_right hD'
  have hv₂ : (v.2:ZMod p)=0 := (mul_eq_zero.mp h₂).resolve_right hD'
  obtain ⟨a,b,hab⟩ := hv
  have hh := congrArg (Int.castRingHom (ZMod p)) hab
  simp only [map_add,map_mul,map_one] at hh
  change (a:ZMod p)*(v.1:ZMod p)+(b:ZMod p)*(v.2:ZMod p)=1 at hh
  rw [hv₁,hv₂,mul_zero,mul_zero,add_zero] at hh
  exact zero_ne_one hh

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
 theorem markedDirtyMajor_det_coordinates (v E F w c : ℤ × ℤ)
    (h₁ : w.1=c.1*E.1+c.2*F.1) (h₂ : w.2=c.1*E.2+c.2*F.2) :
    markedMinorIntegerDet v w=c.1*markedMinorIntegerDet v E+c.2*markedMinorIntegerDet v F := by
  unfold markedMinorIntegerDet
  rw [h₁,h₂]
  ring

 /- Actual targets hitting one specified old particle occupy at most
area/p plus the longer box side. The coordinate injection and reconstruction
are literal integer geometry, with no counting hypothesis. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
 theorem markedDirtyMajor_particle_targets_count {P : Finset Nat.Primes}
    (particle : MarkedRawParticle P) (V : Finset (ℤ × ℤ))
    (hV : ∀ v ∈ V, IsCoprime v.1 v.2) (E F : ℤ × ℤ)
    (hD : ¬((particle.1.1:ℕ):ℤ) ∣ markedMinorIntegerDet E F)
    (coord : ℤ × ℤ → ℤ × ℤ) (hinj : Set.InjOn coord ↑V)
    (hcoord : ∀ v ∈ V, v.1=(coord v).1*E.1+(coord v).2*F.1 ∧
      v.2=(coord v).1*E.2+(coord v).2*F.2)
    (lo hi : ℤ) (M N : ℕ) (hbox : ∀ v ∈ V, coord v ∈ markedMinorBox lo hi M N)
    (hhits : ∀ v (hv : v ∈ V), MarkedRawParticleHits P v (hV v hv) particle) :
    (V.card:ℝ) ≤ (M:ℝ)*N/(particle.1.1:ℕ)+max (M:ℝ) N := by
  classical
  by_cases hnon : V.Nonempty
  · obtain ⟨v₀,hv₀⟩ := hnon
    let p : ℕ := particle.1.1
    let A : ZMod p := markedMinorIntegerDet v₀ E
    let B : ZMod p := markedMinorIntegerDet v₀ F
    have hAB : A ≠ 0 ∨ B ≠ 0 := markedDirtyMajor_line_coefficients particle.1.1.2 v₀ E F (hV v₀ hv₀) hD
    have himg : V.image coord ⊆ markedDirtyMajorLineBox p A B lo hi M N := by
      intro c hc
      obtain ⟨v,hv,rfl⟩ := mem_image.mp hc
      refine mem_filter.mpr ⟨hbox v hv,?_⟩
      have hsame := markedRawParticleHits_same_line particle v₀ v (hV v₀ hv₀) (hV v hv)
        (hhits v₀ hv₀) (hhits v hv)
      have hz : (markedMinorIntegerDet v₀ v:ZMod p)=0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (markedMinorSamePrimeLine_dvd p v₀ v hsame)
      rw [markedDirtyMajor_det_coordinates v₀ E F v (coord v) (hcoord v hv).1 (hcoord v hv).2,
        Int.cast_add,Int.cast_mul,Int.cast_mul] at hz
      simpa only [A,B,mul_comm] using hz
    have hcard : V.card=(V.image coord).card := (card_image_iff.mpr hinj).symm
    rw [hcard]
    exact (show ((V.image coord).card:ℝ) ≤ (markedDirtyMajorLineBox p A B lo hi M N).card by
      exact_mod_cast card_le_card himg).trans (markedDirtyMajorLineBox_count particle.1.1.2 A B hAB lo hi M N)
  · rw [not_nonempty_iff_eq_empty.mp hnon,card_empty,Nat.cast_zero]
    exact add_nonneg (by positivity) (le_max_of_le_left (Nat.cast_nonneg M))

end
end ArtinMatthews

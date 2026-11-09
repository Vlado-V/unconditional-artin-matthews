module

public import ArtinMatthews.MarkedMinorArcSharedLattice


set_option backward.privateInPublic true
@[expose] public section

/-! The residue scalar relation is exactly equality of primitive projective
lines, equivalently the actual vanishing determinant modulo the prime. -/
namespace ArtinMatthews

/-- For primitive vectors, the actual nonzero residue scalar relation is
equivalent to determinant divisibility. The proof uses the genuine integer
completion, not a hypothesized projective distribution. -/
theorem markedMinorSamePrimeLine_iff_dvd {p : ℕ} (hp : p.Prime)
    (z w v : ℤ × ℤ) (hd : markedMinorIntegerDet z w=1)
    (hv : IsCoprime v.1 v.2) :
    MarkedMinorSamePrimeLine p z v ↔ (p : ℤ) ∣ markedMinorIntegerDet z v := by
  constructor
  · exact markedMinorSamePrimeLine_dvd p z v
  · intro hdiv
    have : Fact p.Prime := ⟨hp⟩
    let c : ZMod p := markedMinorIntegerDet v w
    have hj : (markedMinorIntegerDet z v : ZMod p)=0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv
    have hz := markedMinorIntegerBasis_decompose z w v hd
    have h₁ : (v.1 : ZMod p)=c*(z.1 : ZMod p) := by
      have hh := congrArg (Int.castRingHom (ZMod p)) hz.1
      simp only [map_add,map_mul] at hh
      change (v.1 : ZMod p)=(markedMinorIntegerDet v w : ZMod p)*(z.1 : ZMod p)+
        (markedMinorIntegerDet z v : ZMod p)*(w.1 : ZMod p) at hh
      simpa only [hj,zero_mul,add_zero] using hh
    have h₂ : (v.2 : ZMod p)=c*(z.2 : ZMod p) := by
      have hh := congrArg (Int.castRingHom (ZMod p)) hz.2
      simp only [map_add,map_mul] at hh
      change (v.2 : ZMod p)=(markedMinorIntegerDet v w : ZMod p)*(z.2 : ZMod p)+
        (markedMinorIntegerDet z v : ZMod p)*(w.2 : ZMod p) at hh
      simpa only [hj,zero_mul,add_zero] using hh
    refine ⟨c,?_,h₁,h₂⟩
    intro hc
    obtain ⟨a,b,hab⟩ := hv
    have hab' : (a : ZMod p)*(v.1 : ZMod p)+(b : ZMod p)*(v.2 : ZMod p)=1 := by
      have hh := congrArg (Int.castRingHom (ZMod p)) hab
      simp only [map_add,map_mul,map_one] at hh
      change (a : ZMod p)*(v.1 : ZMod p)+(b : ZMod p)*(v.2 : ZMod p)=1 at hh
      exact hh
    rw [h₁,h₂,hc,zero_mul,zero_mul,mul_zero,mul_zero,zero_add] at hab'
    exact zero_ne_one hab'

end ArtinMatthews

module

public import ArtinMatthews.SpectralCuspEisensteinRows


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine parabolic right-orbits of actual bottom rows. The residue modulus
is the target width times the positive integral lower entry. -/
noncomputable section
open Matrix Set
open scoped MatrixGroups
namespace ArtinMatthews

abbrev CuspEisensteinPositiveRows (N : ℕ) (r a : SL(2,ℤ)) :=
  {v : Gamma0CuspEisensteinRows N r a // 0 < v.val 0}

abbrev CuspEisensteinRowFibre (N : ℕ) (r a : SL(2,ℤ)) (c : ℕ) :=
  {d : ℤ // ![(c:ℤ),d] ∈ range (gamma0CuspEisensteinRow N r a)}

theorem cuspEisensteinRowFibre_translate (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (c : ℕ) (d : CuspEisensteinRowFibre N r a c) (k : ℤ) :
    ![(c:ℤ),d.val+(gamma0CuspTrueWidth N r:ℤ)*c*k] ∈
      range (gamma0CuspEisensteinRow N r a) := by
  obtain ⟨M,hM⟩ := d.property
  let T := integerTranslation ((gamma0CuspTrueWidth N r:ℤ)*k)
  have h0 : integerTranslation 0 = (1:SL(2,ℤ)) := by simp [integerTranslation_eq_T_zpow]
  have hm := gamma0CuspCorrespondence_trueWidth_translate N r a M.val M.property 0 k
  simp only [mul_zero,h0,one_mul] at hm
  refine ⟨⟨M.val*T,hm⟩,?_⟩
  have hc : M.val 1 0 = c := congrFun hM 0
  have hd : M.val 1 1 = d.val := congrFun hM 1
  have h := integerTranslation_entries 0 ((gamma0CuspTrueWidth N r:ℤ)*k) M.val
  simp only [h0,one_mul] at h
  funext j
  fin_cases j
  · exact h.2.1.trans hc
  · change (M.val*T : SL(2,ℤ)) 1 1 = d.val+(gamma0CuspTrueWidth N r:ℤ)*c*k
    exact h.2.2.trans (by rw [hc,hd]; ring)

abbrev CuspEisensteinRowResidues (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (c : ℕ) :=
  {d : Fin (gamma0CuspTrueWidth N r*c) //
    ![(c:ℤ),(d.val:ℤ)] ∈ range (gamma0CuspEisensteinRow N r a)}

instance cuspEisensteinRowResidues_fintype (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (c : ℕ) : Fintype (CuspEisensteinRowResidues N r a c) :=
  Fintype.ofFinite _

def cuspEisensteinResidueTranslate (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (c : ℕ) (p : CuspEisensteinRowResidues N r a c × ℤ) :
    CuspEisensteinRowFibre N r a c :=
  ⟨(p.1.val.val:ℤ)+(gamma0CuspTrueWidth N r:ℤ)*c*p.2,
    cuspEisensteinRowFibre_translate N r a c ⟨p.1.val.val,p.1.property⟩ p.2⟩

def cuspEisensteinResidueRemainder (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (c : ℕ) (hc : 0 < c) (d : CuspEisensteinRowFibre N r a c) :
    CuspEisensteinRowResidues N r a c := by
  let L := gamma0CuspTrueWidth N r*c
  have hL : 0 < L := Nat.mul_pos (gamma0CuspTrueWidth_pos N r) hc
  have hLZ : 0 < (L:ℤ) := by exact_mod_cast hL
  have hnonneg := Int.emod_nonneg d.val hLZ.ne'
  have hlt := Int.emod_lt_of_pos d.val hLZ
  have ht : ((d.val%(L:ℤ)).toNat:ℤ)=d.val%(L:ℤ) := Int.toNat_of_nonneg hnonneg
  refine ⟨⟨(d.val%(L:ℤ)).toNat,?_⟩,?_⟩
  · change (d.val%(L:ℤ)).toNat < L
    exact_mod_cast (show ((d.val%(L:ℤ)).toNat:ℤ)<L by rw [ht]; exact hlt)
  have hp := cuspEisensteinRowFibre_translate N r a c d (-(d.val/(L:ℤ)))
  have he : d.val+(gamma0CuspTrueWidth N r:ℤ)*c*(-(d.val/(L:ℤ)))=d.val%(L:ℤ) := by
    have h := Int.emod_add_mul_ediv d.val (L:ℤ)
    dsimp [L] at *
    nlinarith
  simpa only [ht,he] using hp

def cuspEisensteinResidueTranslateEquiv (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (c : ℕ) (hc : 0 < c) :
    (CuspEisensteinRowResidues N r a c × ℤ) ≃ CuspEisensteinRowFibre N r a c where
  toFun := cuspEisensteinResidueTranslate N r a c
  invFun d := (cuspEisensteinResidueRemainder N r a c hc d,
    d.val/((gamma0CuspTrueWidth N r:ℤ)*c))
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      apply Fin.ext
      change (((p.1.val.val:ℤ)+(gamma0CuspTrueWidth N r:ℤ)*c*p.2)%
        ((gamma0CuspTrueWidth N r*c:ℕ):ℤ)).toNat = p.1.val.val
      have hnonneg : (0:ℤ) ≤ p.1.val.val := by positivity
      have hlt : (p.1.val.val:ℤ)<(gamma0CuspTrueWidth N r:ℤ)*c := by
        exact_mod_cast p.1.val.isLt
      simp only [Nat.cast_mul,Int.add_emod,Int.mul_emod,Int.emod_self,zero_mul,
        Int.zero_emod,add_zero,Int.emod_eq_of_lt hnonneg hlt,Int.toNat_natCast]
    · change ((p.1.val.val:ℤ)+(gamma0CuspTrueWidth N r:ℤ)*c*p.2)/
        ((gamma0CuspTrueWidth N r:ℤ)*c)=p.2
      have hL : 0 < (gamma0CuspTrueWidth N r:ℤ)*c := mul_pos
        (by exact_mod_cast gamma0CuspTrueWidth_pos N r) (by exact_mod_cast hc)
      rw [Int.add_mul_ediv_left _ _ hL.ne']
      have hz : (p.1.val.val:ℤ)/((gamma0CuspTrueWidth N r:ℤ)*c)=0 :=
        Int.ediv_eq_zero_of_lt_abs (by positivity) (by rw [abs_of_pos hL]; exact_mod_cast p.1.val.isLt)
      omega
  right_inv d := by
    apply Subtype.ext
    change (((d.val%((gamma0CuspTrueWidth N r*c:ℕ):ℤ)).toNat:ℤ)+
      (gamma0CuspTrueWidth N r:ℤ)*c*(d.val/((gamma0CuspTrueWidth N r:ℤ)*c)))=d.val
    have hL : (0:ℤ) < ((gamma0CuspTrueWidth N r*c:ℕ):ℤ) := by
      exact_mod_cast Nat.mul_pos (gamma0CuspTrueWidth_pos N r) hc
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hL.ne')]
    simpa only [Nat.cast_mul] using Int.emod_add_mul_ediv d.val
      ((gamma0CuspTrueWidth N r:ℤ)*c)

end ArtinMatthews

module

public import ArtinMatthews.MarkedMinorArcRawLinePartition
public import ArtinMatthews.MarkedMinorArcRawGoodFirst
public import ArtinMatthews.MarkedMinorArcDirtyAnchor
public import ArtinMatthews.MarkedMinorArcDirtyPermutation


set_option backward.privateInPublic true
@[expose] public section

/-! The distinguished actual indexed particle supplies the common dirty
anchor residue. Its abstract projective anchor needs no integer lift. -/
namespace ArtinMatthews

open scoped BigOperators

theorem markedRawParticleHits_same_line {P : Finset Nat.Primes} (a : MarkedRawParticle P)
    (z v : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (hv : IsCoprime v.1 v.2)
    (ha : MarkedRawParticleHits P z hz a) (hb : MarkedRawParticleHits P v hv a) :
    MarkedMinorSamePrimeLine (a.1.1:ℕ) z v := by
  apply (markedPrimePositionLine_eq_iff_same (a.1.1:ℕ) z v hz hv).mp
  exact ha.symm.trans hb

/-- The literal cross-edge ban makes the distinguished promoted prime
invertible against the full actual source product. -/
theorem markedRawSourceFull_not_dvd_of_cross_ban {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M : ℕ} (source : MarkedRawActive P M)
    {Q : Finset Nat.Primes} (a : MarkedRawParticle Q)
    (hban : ∀ j k, (source j k).1 ≠ a.1.1) :
    ¬((a.1.1:ℕ):ℤ) ∣ (markedSourceFullProduct (markedRawNumericActive source):ℤ) := by
  have hc := markedSourceFull_coprime_promoted_of_cross_ban (R := Unit)
    (markedRawNumericActive source) (fun j k => (source j k).1.2)
    (fun _ => (a.1.1:ℕ)) (fun _ => a.1.1.2)
    (fun j k _ he => hban j k (Subtype.ext he))
  have hcn : (markedSourceFullProduct (markedRawNumericActive source)).Coprime (a.1.1:ℕ) := by
    simpa only [Fintype.prod_unique] using hc
  have hn := a.1.1.2.coprime_iff_not_dvd.mp hcn.symm
  simpa only [Int.natCast_dvd_natCast] using hn

/-- For the actual particle anchor, any two compatible dirty numeric choices
have exactly the same h residue; omissions and all other promoted labels
are absent from that residue. -/
theorem markedRawDirty_anchor_residue_unique {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} (source : MarkedRawActive P M)
    (memory : MarkedRawMemory P B) (jstar : J) (kstar : Fin (memory.1.1 jstar:ℕ))
    (hban : ∀ j k, (source j k).1 ≠ (memory.2 jstar kstar).1.1)
    (D₁ D₂ Z₁ Z₂ T₁ T₂ h₁ h₂ : ℤ) (z w : ℤ × ℤ)
    (hd : markedMinorIntegerDet z w=1)
    (hv₁ : IsCoprime
      (markedMinorDirtyPosition z w h₁ (markedMinorDirtyDeterminant
        (markedSourceFullProduct (markedRawNumericActive source):ℤ) D₁ ((memory.2 jstar kstar).1.1:ℕ) Z₁ T₁)).1
      (markedMinorDirtyPosition z w h₁ (markedMinorDirtyDeterminant
        (markedSourceFullProduct (markedRawNumericActive source):ℤ) D₁ ((memory.2 jstar kstar).1.1:ℕ) Z₁ T₁)).2)
    (hv₂ : IsCoprime
      (markedMinorDirtyPosition z w h₂ (markedMinorDirtyDeterminant
        (markedSourceFullProduct (markedRawNumericActive source):ℤ) D₂ ((memory.2 jstar kstar).1.1:ℕ) Z₂ T₂)).1
      (markedMinorDirtyPosition z w h₂ (markedMinorDirtyDeterminant
        (markedSourceFullProduct (markedRawNumericActive source):ℤ) D₂ ((memory.2 jstar kstar).1.1:ℕ) Z₂ T₂)).2)
    (ha : MarkedRawParticleHits (P jstar)
      (markedMinorDirtyPosition z w h₁ (markedMinorDirtyDeterminant
        (markedSourceFullProduct (markedRawNumericActive source):ℤ) D₁ ((memory.2 jstar kstar).1.1:ℕ) Z₁ T₁)) hv₁
      (memory.2 jstar kstar))
    (hb : MarkedRawParticleHits (P jstar)
      (markedMinorDirtyPosition z w h₂ (markedMinorDirtyDeterminant
        (markedSourceFullProduct (markedRawNumericActive source):ℤ) D₂ ((memory.2 jstar kstar).1.1:ℕ) Z₂ T₂)) hv₂
      (memory.2 jstar kstar)) :
    (h₁ : ZMod ((memory.2 jstar kstar).1.1:ℕ)) =
      (h₂ : ZMod ((memory.2 jstar kstar).1.1:ℕ)) := by
  exact markedMinorDirty_anchor_residue_unique (memory.2 jstar kstar).1.1.2
    _ D₁ D₂ Z₁ Z₂ T₁ T₂ h₁ h₂
    (markedRawSourceFull_not_dvd_of_cross_ban source (memory.2 jstar kstar) hban) z w hd
    (markedRawParticleHits_same_line (memory.2 jstar kstar) _ _ hv₁ hv₂ ha hb)

end ArtinMatthews

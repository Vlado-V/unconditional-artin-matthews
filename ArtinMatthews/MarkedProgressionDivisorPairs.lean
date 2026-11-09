module

public import ArtinMatthews.MarkedProgressionCounting
public import Mathlib.NumberTheory.Divisors


set_option backward.privateInPublic true
@[expose] public section

/-! A pair of divisors embeds into the four-factor decompositions of its
integer. This gives a finite carrier for the squared divisor count on
the actual progression. -/

namespace ArtinMatthews
open scoped BigOperators

abbrev MarkedDivisorTriple := ℕ × ℕ × ℕ
abbrev MarkedDivisorQuadruple := ℕ × ℕ × ℕ × ℕ

def markedDivisorTripleProduct (t : MarkedDivisorTriple) : ℕ :=
  t.1 * t.2.1 * t.2.2

def markedDivisorQuadrupleProduct (t : MarkedDivisorQuadruple) : ℕ :=
  t.1 * t.2.1 * t.2.2.1 * t.2.2.2

def markedDivisorPairFactors (n d e : ℕ) : MarkedDivisorQuadruple :=
  (d.gcd e,d / d.gcd e,e / d.gcd e,n / d.lcm e)

theorem markedDivisorPairFactors_left (n d e : ℕ) :
    (markedDivisorPairFactors n d e).1 * (markedDivisorPairFactors n d e).2.1 = d :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)

theorem markedDivisorPairFactors_right (n d e : ℕ) :
    (markedDivisorPairFactors n d e).1 * (markedDivisorPairFactors n d e).2.2.1 = e :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)

theorem markedDivisorPairFactors_product {n d e : ℕ} (hd : d ∈ n.divisors)
    (he : e ∈ n.divisors) :
    markedDivisorQuadrupleProduct (markedDivisorPairFactors n d e) = n := by
  let g := d.gcd e
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_mem_divisors hd)
  have hde : g * (d/g) * (e/g) = d.lcm e := by
    apply Nat.eq_of_mul_eq_mul_left hg
    calc
      g * (g * (d/g) * (e/g)) = (g * (d/g)) * (g * (e/g)) := by ring
      _ = d * e := by
        rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left d e),
          Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)]
      _ = g * d.lcm e := (Nat.gcd_mul_lcm d e).symm
  change g * (d/g) * (e/g) * (n / d.lcm e) = n
  rw [hde]
  exact Nat.mul_div_cancel' (Nat.lcm_dvd (Nat.dvd_of_mem_divisors hd) (Nat.dvd_of_mem_divisors he))

def markedDivisorTripleBox (X : ℕ) : Finset MarkedDivisorTriple :=
  (Finset.Ioc 0 X).product ((Finset.Ioc 0 X).product (Finset.Ioc 0 X))

def markedDivisorQuadrupleBox (X : ℕ) : Finset MarkedDivisorQuadruple :=
  (Finset.Ioc 0 X).product (markedDivisorTripleBox X)

theorem markedDivisorQuadruple_mem_box {X : ℕ} (t : MarkedDivisorQuadruple)
    (hpos : 0 < markedDivisorQuadrupleProduct t)
    (hX : markedDivisorQuadrupleProduct t ≤ X) : t ∈ markedDivisorQuadrupleBox X := by
  rcases t with ⟨a,b,c,r⟩
  change 0 < a*b*c*r at hpos
  change a*b*c*r ≤ X at hX
  have hne : (a*b*c*r) ≠ 0 := hpos.ne'
  simp only [Nat.mul_ne_zero_iff] at hne
  obtain ⟨⟨⟨ha,hb⟩,hc⟩,hr⟩ := hne
  have ha' := Nat.pos_of_ne_zero ha
  have hb' := Nat.pos_of_ne_zero hb
  have hc' := Nat.pos_of_ne_zero hc
  have hr' := Nat.pos_of_ne_zero hr
  have h_ab := Nat.mul_pos ha' hb'
  have h_abc := Nat.mul_pos h_ab hc'
  have htail : a*b*c ≤ X := (Nat.le_mul_of_pos_right _ hr').trans hX
  have hpair : a*b ≤ X := (Nat.le_mul_of_pos_right _ hc').trans htail
  simp only [markedDivisorQuadrupleBox,markedDivisorTripleBox,Finset.product_eq_sprod,
    Finset.mem_product,Finset.mem_Ioc]
  exact ⟨⟨ha',(Nat.le_mul_of_pos_right _ hb').trans hpair⟩,
    ⟨hb',(Nat.le_mul_of_pos_left _ ha').trans hpair⟩,
    ⟨hc',(Nat.le_mul_of_pos_left _ h_ab).trans htail⟩,
    ⟨hr',(Nat.le_mul_of_pos_left _ h_abc).trans hX⟩⟩

def markedProgressionDivisorIntegers (a X : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 X).filter (fun n => Nat.ModEq a n 1)

def markedProgressionDivisorQuadruples (a X : ℕ) : Finset MarkedDivisorQuadruple :=
  (markedDivisorQuadrupleBox X).filter (fun t =>
    markedDivisorQuadrupleProduct t ≤ X ∧ Nat.ModEq a (markedDivisorQuadrupleProduct t) 1)

theorem markedProgression_divisor_pair_count (a X : ℕ) :
    (∑ n ∈ markedProgressionDivisorIntegers a X, n.divisors.card^2) ≤
      (markedProgressionDivisorQuadruples a X).card := by
  let S := (markedProgressionDivisorIntegers a X).sigma
    (fun n => n.divisors.product n.divisors)
  have hcard : S.card = ∑ n ∈ markedProgressionDivisorIntegers a X, n.divisors.card^2 := by
    simp only [S,Finset.card_sigma,Finset.product_eq_sprod,Finset.card_product,pow_two]
  rw [← hcard]
  apply Finset.card_le_card_of_injOn (fun p : Σ _ : ℕ, ℕ × ℕ => markedDivisorPairFactors p.1 p.2.1 p.2.2)
  · rintro ⟨n,d,e⟩ hs
    obtain ⟨hn,hde⟩ := Finset.mem_sigma.mp hs
    obtain ⟨hd,he⟩ := Finset.mem_product.mp hde
    obtain ⟨hn,hmod⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn0,hnX⟩ := Finset.mem_Ioc.mp hn
    have hprod := markedDivisorPairFactors_product hd he
    exact Finset.mem_filter.mpr ⟨markedDivisorQuadruple_mem_box _ (hprod.symm ▸ hn0)
      (hprod.symm ▸ hnX),hprod.symm ▸ hnX,hprod.symm ▸ hmod⟩
  · rintro ⟨n,d,e⟩ hp ⟨m,f,g⟩ hq h
    have hp' := Finset.mem_product.mp (Finset.mem_sigma.mp hp).2
    have hq' := Finset.mem_product.mp (Finset.mem_sigma.mp hq).2
    have hnm : n = m := (markedDivisorPairFactors_product hp'.1 hp'.2).symm.trans
      ((congrArg markedDivisorQuadrupleProduct h).trans (markedDivisorPairFactors_product hq'.1 hq'.2))
    have hdf : d = f := (markedDivisorPairFactors_left n d e).symm.trans
      ((congrArg (fun t : MarkedDivisorQuadruple => t.1*t.2.1) h).trans
        (markedDivisorPairFactors_left m f g))
    have heg : e = g := (markedDivisorPairFactors_right n d e).symm.trans
      ((congrArg (fun t : MarkedDivisorQuadruple => t.1*t.2.2.1) h).trans
        (markedDivisorPairFactors_right m f g))
    cases hnm
    cases hdf
    cases heg
    rfl

end ArtinMatthews

open HolKernel Parse boolLib bossLib;
open ETCSaxiomTheory basicTheory Thm1Theory Thm2Theory Thm3Theory;

val _ = new_theory "Thm5";



Theorem Thm5_lemma_1:
∀A X a x. is_mono a ∧ a∶ A → X ∧ x∶ one → X ∧
          ¬(∃x0. x0∶ one → A ∧ a o x0 = x) ⇒
          ∃phi. phi∶ X → (one + one) ∧
                phi o x = i2 one one ∧
                phi o a = (i1 one one) o (to1 A)
Proof
rw[] >>
‘¬((A + one) ≅ zero)’ by metis_tac[i2_hom,iso_zero_no_mem] >>
‘∃a1. a1∶ one → A + one’ by metis_tac[ax6] >>
‘copa a x∶ (A + one) → X’ by metis_tac[copa_hom] >>
‘∃u. u∶ X → (A + one) ∧ copa a x o u o copa a x = copa a x’ by metis_tac[ax5] >>
qabbrev_tac ‘ta = copa ((i1 one one) o (to1 A)) (i2 one one)’ >>
qexists_tac ‘ta o u’ >>
‘(i2 one one)∶ one → one + one’ by metis_tac[i2_hom] >>
‘(i1 one one)∶ one → one + one’ by metis_tac[i1_hom] >>
‘to1 A∶ A → one’ by metis_tac[ax1_1] >>
‘(i1 one one ∘ to1 A)∶ A → one + one’ by metis_tac[compose_hom] >> 
‘ta∶ (A + one) → one + one’ by (simp[Abbr‘ta’] >> metis_tac[copa_hom]) >>
‘ta ∘ u∶X → one + one’ by metis_tac[compose_hom] >> simp[] >>
‘is_mono (copa a x)’ by metis_tac[copa_not_mem_mono_mono] >>
‘u ∘ copa a x = id (A + one)’ by metis_tac[mono_pinv_post_inv] >>
‘x = copa a x o i2 A one’ by metis_tac[i2_of_copa] >>
‘a = copa a x o i1 A one’ by metis_tac[i1_of_copa] >> 
‘(ta ∘ u) ∘ copa a x ∘ i2 A one = i2 one one ∧
 (ta ∘ u) ∘ copa a x ∘ i1 A one = i1 one one ∘ to1 A’ suffices_by metis_tac[] >>
‘i1 A one∶ A → (A + one) ∧ i2 A one∶ one → (A + one)’ by metis_tac[i1_hom,i2_hom]>>
‘(ta ∘ u) ∘ copa a x ∘ i2 A one = ta ∘ u ∘ copa a x ∘ i2 A one’
  by metis_tac[compose_assoc_4_2_left] >>
‘u ∘ copa a x ∘ i2 A one = (u ∘ copa a x) ∘ i2 A one’ by metis_tac[compose_assoc]>>
simp[] >>
‘(ta ∘ u) ∘ copa a x ∘ i1 A one = ta ∘ u ∘ copa a x ∘ i1 A one’
  by metis_tac[compose_assoc_4_2_left] >>
‘u ∘ copa a x ∘ i1 A one = (u ∘ copa a x) ∘ i1 A one’ by metis_tac[compose_assoc]>>
simp[] >>
‘ta ∘ id (A + one) ∘ i2 A one = ta ∘ i2 A one ∧
 ta ∘ id (A + one) ∘ i1 A one = ta ∘ i1 A one’
  by metis_tac[id1,idL,idR,compose_assoc] >> simp[] >>
simp[Abbr‘ta’] >> metis_tac[i1_of_copa,i2_of_copa]
QED                


Theorem Thm5:
∀A X a. is_mono a ∧ a∶ A → X ⇒
        ∃A' a'. is_mono a' ∧ a'∶ A' → X ∧ is_iso (copa a a')
Proof        
rw[] >>
‘i1 one one∶ one → (one + one) ∧ i2 one one∶ one → (one + one)’
  by metis_tac[i1_hom,i2_hom] >>
‘to1 (A× one)∶ (A × one) → one’ by metis_tac[ax1_1] >>
‘(i1 one one) o to1 (A× one)∶ (A× one) → (one + one)’
  by metis_tac[compose_hom] >> 
qabbrev_tac ‘j0 = tp ((i1 one one) o to1 (A× one))’ >>
‘j0∶ one → exp A (one + one)’
  by (simp[Abbr‘j0’] >> metis_tac[tp_hom]) >>
‘to1 (exp X (one + one))∶ (exp X (one + one)) → one’
  by metis_tac[ax1_1] >>
‘j0 o to1 (exp X (one + one))∶ (exp X (one + one)) → exp A (one + one)’ by metis_tac[compose_hom] >>
‘ev X (one + one)∶ (X × (exp X (one + one))) → (one + one)’
  by metis_tac[ev_hom] >>
qabbrev_tac ‘two = one + one’ >>
‘p1 A (exp X two)∶  A × (exp X two) → A ∧
 p2 A (exp X two)∶  A × (exp X two) → (exp X two)’
  by metis_tac[p1_hom,p2_hom] >>
‘a o p1 A (exp X two)∶ A × (exp X two) → X’
 by metis_tac[compose_hom] >> 
‘⟨a o p1 A (exp X two), p2 A (exp X two)⟩∶
 (A× (exp X two)) → (X× (exp X two))’ by metis_tac[pa_hom]>>
‘ev X two o ⟨a o p1 A (exp X two), p2 A (exp X two)⟩∶
 (A× (exp X two)) → two’ by metis_tac[compose_hom] >>
qabbrev_tac
‘a2 = tp (ev X two o ⟨a o p1 A (exp X two), p2 A (exp X two)⟩)’>>
‘a2∶ exp X two → exp A two’
 by (simp[Abbr‘a2’] >> metis_tac[tp_hom]) >>
qabbrev_tac ‘μ = eqa a2 (j0 ∘ to1 (exp X two))’ >>
qabbrev_tac ‘L = eqo a2 (j0 ∘ to1 (exp X two))’ >>
‘μ∶ L → exp X two’
 by (simp[Abbr‘L’,Abbr‘μ’] >> metis_tac[eqa_hom]) >>
‘p1 X L∶ (X× L) → X ∧ p2 X L∶ (X × L) → L’
 by metis_tac[p1_hom,p2_hom] >>
‘(μ o p2 X L)∶ (X × L) → (exp X two)’
 by metis_tac[compose_hom] >>
qabbrev_tac ‘ub = (ev X two) o ⟨p1 X L, μ o p2 X L⟩’ >>
‘⟨p1 X L, μ o p2 X L⟩∶ (X× L) → (X × (exp X two))’
 by metis_tac[pa_hom] >>
‘ub∶ (X× L) → two’ by (simp[Abbr‘ub’] >> metis_tac[compose_hom])>>
‘to1 (X × L)∶ (X × L) → one’ by metis_tac[ax1_1] >>
‘i2 one one o to1 (X × L)∶ (X× L) → two’
 by metis_tac[compose_hom] >>
qabbrev_tac ‘k = eqa ub ((i2 one one) o to1 (X × L))’ >>
qabbrev_tac ‘σ = eqo ub ((i2 one one) o to1 (X × L))’ >>
‘k∶ σ → (X × L)’
 by (simp[Abbr‘k’,Abbr‘σ’] >> metis_tac[eqa_hom])>>
‘p1 X L o k∶ σ → X’ by metis_tac[compose_hom] >> 
‘∃A' a' q. is_epi q ∧ is_mono a' ∧
           q∶ σ → A' ∧ a'∶ A' → X ∧ a' o q = p1 X L o k’
  by (drule mono_epi_fac >> metis_tac[]) >>
qexistsl_tac [‘A'’,‘a'’] >> simp[] >>
irule mono_epi_is_iso >>
‘copa a a'∶ (A + A') → X’ by metis_tac[copa_hom] >>
‘i1 A A'∶ A → (A + A') ∧ i2 A A'∶ A' → (A + A')’
 by metis_tac[i1_hom,i2_hom] >> 
reverse (strip_tac) (* 2 *) >- (* mono*)
(‘(j0 o (to1 (exp X two))) o μ = a2 o μ’
    by (simp[Abbr‘μ’] >> metis_tac[eq_equlity]) >>
‘(ev X two) o ⟨a o p1 A (exp X two), p2 A (exp X two)⟩ =
 (ev A two) o ⟨p1 A (exp X two), a2 o p2 A (exp X two)⟩’
 by
  (simp[Abbr‘a2’] >> metis_tac[ev_of_tp]) >>
‘p1 A L∶ (A × L) → A ∧ p2 A L∶ (A × L) → L’
 by metis_tac[p1_hom,p2_hom] >>
‘μ ∘ p2 A L∶ (A × L) → exp X two’ by metis_tac[compose_hom] >>
‘⟨p1 A L,μ ∘ p2 A L⟩∶ (A × L) → (A × (exp X two))’
 by metis_tac[pa_hom,compose_hom] >>
‘ev A two∶ (A × (exp A two)) → two’ by metis_tac[ev_hom] >>
‘((ev X two) o ⟨a o p1 A (exp X two), p2 A (exp X two)⟩) o
 ⟨p1 A L, μ o p2 A L⟩ =
 ((ev A two) o ⟨p1 A (exp X two), a2 o p2 A (exp X two)⟩) o
 ⟨p1 A L, μ o p2 A L⟩’
 by metis_tac[] >>
‘ev X two ∘ ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩ ∘
        ⟨p1 A L,μ ∘ p2 A L⟩ =
 (ev X two ∘ ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩) ∘
        ⟨p1 A L,μ ∘ p2 A L⟩’ by metis_tac[compose_assoc] >>
‘⟨p1 A (exp X two),a2 ∘ p2 A (exp X two)⟩∶
 (A × (exp X two)) → (A × (exp A two))’
 by metis_tac[pa_hom,compose_hom] >> 
‘ev A two ∘ ⟨p1 A (exp X two),a2 ∘ p2 A (exp X two)⟩ ∘
        ⟨p1 A L,μ ∘ p2 A L⟩ =
 (ev A two ∘ ⟨p1 A (exp X two),a2 ∘ p2 A (exp X two)⟩) ∘
        ⟨p1 A L,μ ∘ p2 A L⟩’ by metis_tac[compose_assoc] >>
‘ev X two ∘ ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩ ∘
        ⟨p1 A L,μ ∘ p2 A L⟩ =
        ev A two ∘ ⟨p1 A (exp X two),a2 ∘ p2 A (exp X two)⟩ ∘
        ⟨p1 A L,μ ∘ p2 A L⟩’ by metis_tac[] 
 (* lemma later *) >>
‘⟨p1 A (exp X two),a2 ∘ p2 A (exp X two)⟩ ∘ ⟨p1 A L,μ ∘ p2 A L⟩ =
 ⟨p1 A L, a2 o μ o p2 A L⟩’
 by
  (‘⟨p1 A (exp X two),a2 ∘ p2 A (exp X two)⟩ ∘ ⟨p1 A L,μ ∘ p2 A L⟩∶
    (A × L) → (A × (exp A two))’ by metis_tac[compose_hom] >>
   ‘⟨p1 A L,a2 ∘ μ ∘ p2 A L⟩∶ (A × L) → (A × (exp A two))’
    by metis_tac[pa_hom,compose_hom,compose_assoc] >>
   irule to_p_eq_applied >>
   qexistsl_tac [‘A’,‘exp A two’,‘A × L’] >> simp[] >>
   ‘p1 A (exp A two) ∘ ⟨p1 A L,a2 ∘ μ ∘ p2 A L⟩ = p1 A L’
    by metis_tac[compose_hom,p1_of_pa] >>
   ‘p2 A (exp A two) ∘ ⟨p1 A L,a2 ∘ μ ∘ p2 A L⟩ = a2 ∘ μ ∘ p2 A L’
    by metis_tac[compose_hom,p2_of_pa] >>
   simp[] >>
   ‘p1 A (exp A two)∶ (A × (exp A two)) → A’ by metis_tac[p1_hom] >>
   ‘p2 A (exp A two)∶ (A × (exp A two)) → (exp A two)’ by metis_tac[p2_hom] >>
   ‘p1 A (exp A two) ∘ ⟨p1 A (exp X two),a2 ∘ p2 A (exp X two)⟩ ∘
        ⟨p1 A L,μ ∘ p2 A L⟩ =
    (p1 A (exp A two) ∘ ⟨p1 A (exp X two),a2 ∘ p2 A (exp X two)⟩) ∘
        ⟨p1 A L,μ ∘ p2 A L⟩’ by metis_tac[compose_assoc,p1_hom] >>
   ‘p2 A (exp A two) ∘ ⟨p1 A (exp X two),a2 ∘ p2 A (exp X two)⟩ ∘
        ⟨p1 A L,μ ∘ p2 A L⟩ =
    (p2 A (exp A two) ∘ ⟨p1 A (exp X two),a2 ∘ p2 A (exp X two)⟩) ∘
        ⟨p1 A L,μ ∘ p2 A L⟩’ by metis_tac[compose_assoc] >>
   simp[] >>
   ‘a2 ∘ p2 A (exp X two)∶ (A × (exp X two)) → exp A two’
    by metis_tac[compose_hom] >>
   ‘p1 A (exp A two) ∘ ⟨p1 A (exp X two),a2 ∘ p2 A (exp X two)⟩ =
    p1 A (exp X two)’ by metis_tac[p1_of_pa] >>
   ‘p2 A (exp A two) ∘ ⟨p1 A (exp X two),a2 ∘ p2 A (exp X two)⟩ =
    a2 ∘ p2 A (exp X two)’ by metis_tac[p2_of_pa] >>
   simp[] >>
   rw[] (* 2 *)
   >- metis_tac[p1_of_pa]
   >- (‘(a2 ∘ p2 A (exp X two)) ∘ ⟨p1 A L,μ ∘ p2 A L⟩ =
       a2 ∘ p2 A (exp X two) ∘ ⟨p1 A L,μ ∘ p2 A L⟩’
        by metis_tac[compose_assoc] >>
      simp[] >>
      metis_tac[p2_of_pa])
   ) >>
‘a2 o μ∶ L → exp A two’ by metis_tac[compose_hom] >>
‘∀x. x∶ one → X ∧ (∃x0. x0∶ one → A ∧ a o x0 = x) ⇒
    ∀t. t∶ one → exp X two ∧
        (∃t0. t0∶ one → L ∧ μ o t0 = t) ⇒
        ev X two o ⟨x,t⟩ = i1 one one’
 by
  (rw[] >>
   ‘⟨a ∘ x0,μ ∘ t0⟩∶ one → (X × (exp X two))’
     by metis_tac[compose_hom,pa_hom] >>
   ‘⟨x0,t0⟩∶ one → (A × L)’ by metis_tac[pa_hom] >>
   ‘⟨a o p1 A (exp X two), p2 A (exp X two)⟩ o
    ⟨p1 A L, μ o p2 A L⟩ o ⟨x0,t0⟩∶ one → (X × (exp X two))’
     by metis_tac[compose_hom] >> 
   ‘⟨a ∘ x0,μ ∘ t0⟩ =
    ⟨a o p1 A (exp X two), p2 A (exp X two)⟩ o
    ⟨p1 A L, μ o p2 A L⟩ o ⟨x0,t0⟩’
    by (irule to_p_eq_applied >>
       qexistsl_tac [‘X’,‘(exp X two)’,‘one’] >>
       simp[] >>
       ‘p1 X (exp X two) ∘ ⟨a ∘ x0,μ ∘ t0⟩ = a o x0’
        by metis_tac[p1_of_pa] >>
       ‘p2 X (exp X two) ∘ ⟨a ∘ x0,μ ∘ t0⟩ = μ o t0’
        by metis_tac[p2_of_pa] >>
        simp[] >>
        ‘p1 X (exp X two)∶ (X × (exp X two)) → X’
         by metis_tac[p1_hom] >> 
        ‘p1 X (exp X two) ∘ ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩ ∘
         ⟨p1 A L,μ ∘ p2 A L⟩ ∘ ⟨x0,t0⟩ =
         (p1 X (exp X two) ∘
         ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩) ∘
         ⟨p1 A L,μ ∘ p2 A L⟩ ∘ ⟨x0,t0⟩’
         by metis_tac[compose_assoc_4_2_left] >>
        ‘p2 X (exp X two)∶ (X × (exp X two)) → exp X two’
         by metis_tac[p2_hom] >>
        ‘p2 X (exp X two) ∘ ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩ ∘
         ⟨p1 A L,μ ∘ p2 A L⟩ ∘ ⟨x0,t0⟩ =
         (p2 X (exp X two) ∘
         ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩) ∘
         ⟨p1 A L,μ ∘ p2 A L⟩ ∘ ⟨x0,t0⟩’
         by metis_tac[compose_assoc_4_2_left] >>
        simp[] >>
        ‘p1 X (exp X two) ∘ ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩ =
        a o p1 A (exp X two)’ by metis_tac[p1_of_pa] >>
        ‘p2 X (exp X two) ∘ ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩ =
        p2 A (exp X two)’ by metis_tac[p2_of_pa] >>
        simp[] >>
        ‘p2 A (exp X two) ∘ ⟨p1 A L,μ ∘ p2 A L⟩ ∘ ⟨x0,t0⟩ =
         (p2 A (exp X two) ∘ ⟨p1 A L,μ ∘ p2 A L⟩) ∘ ⟨x0,t0⟩’
         by metis_tac[compose_assoc] >>
        ‘(p2 A (exp X two) ∘ ⟨p1 A L,μ ∘ p2 A L⟩)  = μ o p2 A L’
         by metis_tac[p2_of_pa] >>
        simp[] >>
        reverse (rw[]) (* 2 *)
        >- metis_tac[p2_of_pa,compose_assoc]
        >- (‘(a ∘ p1 A (exp X two)) ∘ ⟨p1 A L,μ ∘ p2 A L⟩ ∘ ⟨x0,t0⟩ =
            a ∘ (p1 A (exp X two) ∘ ⟨p1 A L,μ ∘ p2 A L⟩) ∘ ⟨x0,t0⟩’
             by metis_tac[compose_assoc_4_2_left_middle] >>
           simp[] >>
           ‘p1 A (exp X two) ∘ ⟨p1 A L,μ ∘ p2 A L⟩ = p1 A L’
            by metis_tac[p1_of_pa] >>
           simp[] >>
           metis_tac[p1_of_pa])) >>
   rw[] >>
   ‘ev X two ∘ ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩ ∘
        ⟨p1 A L,μ ∘ p2 A L⟩ ∘ ⟨x0,t0⟩ =
    (ev X two ∘ ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩ ∘
        ⟨p1 A L,μ ∘ p2 A L⟩) ∘ ⟨x0,t0⟩’
     by metis_tac[compose_assoc_4_3_left] >>
   rw[] >>
   ‘(ev A two ∘ ⟨p1 A L,a2 ∘ μ ∘ p2 A L⟩) =
    (ev A two ∘ ⟨p1 A L,(a2 ∘ μ) ∘ p2 A L⟩)’
     by metis_tac[compose_assoc,p2_hom] >>
   simp[] >>
   ‘(ev A two ∘ ⟨p1 A L, ((j0 ∘ to1 (exp X two)) ∘ μ) ∘ p2 A L⟩) o ⟨x0, t0⟩ = i1 one one’ suffices_by metis_tac[] >>
   ‘⟨p1 A L, ((j0 ∘ to1 (exp X two)) ∘ μ) ∘ p2 A L⟩ =
    ⟨p1 A one, j0 o p2 A one ⟩ o ⟨p1 A L,(to1 (exp X two)) o μ o p2 A L⟩’ by
    (irule to_p_eq_applied >>
    qexistsl_tac [‘A’,‘exp A two’,‘A × L’] >>
    ‘⟨p1 A L,((j0 ∘ to1 (exp X two)) ∘ μ) ∘ p2 A L⟩∶(A × L) →  (A × (exp A two))’ by metis_tac[pa_hom,compose_hom] >>
    ‘⟨p1 A one,j0 ∘ p2 A one⟩∶ (A × one) → (A × (exp A two))’
      by metis_tac[compose_hom,pa_hom,p2_hom,p1_hom] >>
    ‘⟨p1 A L,to1 (exp X two) ∘ μ ∘ p2 A L⟩∶ (A × L) → (A × one)’
      by metis_tac[pa_hom,compose_hom] >>
    ‘⟨p1 A one,j0 ∘ p2 A one⟩ ∘ ⟨p1 A L,to1 (exp X two) ∘ μ ∘ p2 A L⟩∶A ×  L → (A × exp A two)’ by metis_tac[compose_hom] >>
    simp[] >>
    ‘p1 A (exp A two) ∘ ⟨p1 A L,(a2 ∘ μ) ∘ p2 A L⟩ = p1 A L’
     by metis_tac[p1_of_pa,compose_hom,p2_hom,p1_hom] >>
    ‘p2 A (exp A two) ∘ ⟨p1 A L,(a2 ∘ μ) ∘ p2 A L⟩ =
     (a2 ∘ μ) ∘ p2 A L’ by metis_tac[p1_of_pa,p2_of_pa,compose_hom,p1_hom,p2_hom] >>
     simp[] >>
     ‘⟨p1 A L,to1 (exp X two) ∘ μ ∘ p2 A L⟩∶ (A × L) →
      (A × one)’ by metis_tac[pa_hom,compose_hom] >>
     ‘⟨p1 A one,j0 ∘ p2 A one⟩∶ (A × one) → (A × (exp A two))’
      by metis_tac[pa_hom,compose_hom,p1_hom,p2_hom] >> 
     ‘p1 A (exp A two) ∘ ⟨p1 A one,j0 ∘ p2 A one⟩ ∘
        ⟨p1 A L,to1 (exp X two) ∘ μ ∘ p2 A L⟩ =
      (p1 A (exp A two) ∘ ⟨p1 A one,j0 ∘ p2 A one⟩) ∘
        ⟨p1 A L,to1 (exp X two) ∘ μ ∘ p2 A L⟩’
       by metis_tac[compose_assoc,p1_hom] >>
     simp[] >>
     ‘p1 A one∶ (A × one)→ A ∧ p2 A one∶ (A × one) → one’
      by metis_tac[p1_hom,p2_hom] >>
     ‘j0 ∘ p2 A one∶ (A × one) → exp A two’
      by metis_tac[compose_hom] >>
     ‘p1 A (exp A two) ∘ ⟨p1 A one,j0 ∘ p2 A one⟩ =
      p1 A one’ by metis_tac[p1_of_pa] >>
     simp[] >>
     ‘p2 A (exp A two)∶ (A × (exp A two)) → exp A two’
      by metis_tac[p2_hom] >>
     ‘p2 A (exp A two) ∘ ⟨p1 A one,j0 ∘ p2 A one⟩ ∘
        ⟨p1 A L,to1 (exp X two) ∘ μ ∘ p2 A L⟩ =
      (p2 A (exp A two) ∘ ⟨p1 A one,j0 ∘ p2 A one⟩) ∘
        ⟨p1 A L,to1 (exp X two) ∘ μ ∘ p2 A L⟩’
       by metis_tac[compose_assoc] >>
     simp[] >>
     ‘(p2 A (exp A two)) ∘ ⟨p1 A one,j0 ∘ p2 A one⟩ =
      (j0 o p2 A one)’ by metis_tac[p2_of_pa] >>
     simp[] >>
     ‘(j0 ∘ p2 A one) ∘ ⟨p1 A L,to1 (exp X two) ∘ μ ∘ p2 A L⟩ =
      j0 ∘ p2 A one ∘ ⟨p1 A L,to1 (exp X two) ∘ μ ∘ p2 A L⟩’
       by metis_tac[compose_assoc] >>
     ‘p2 A one ∘ ⟨p1 A L,to1 (exp X two) ∘ μ ∘ p2 A L⟩ =
      to1 (exp X two) ∘ μ ∘ p2 A L’
       by metis_tac[p2_of_pa,compose_hom] >>
     simp[] >>
     rw[] (* 2 *)
     >- metis_tac[p1_of_pa,compose_hom]
     >- (‘((j0 ∘ to1 (exp X two)) ∘ μ) o p2 A L =
         j0 ∘ to1 (exp X two) ∘ μ ∘ p2 A L’
          suffices_by metis_tac[] >>
        ‘(j0 ∘ to1 (exp X two)) ∘ μ =
         j0 ∘ to1 (exp X two) ∘ μ’ by metis_tac[compose_assoc] >>
        simp[] >>
        metis_tac[compose_assoc_4_3_left])) >>
   ‘p1 A one∶ (A × one) → A ∧ p2 A one∶ (A × one) → one’
    by metis_tac[p1_hom,p2_hom] >> 
   ‘⟨p1 A one,j0 ∘ p2 A one⟩∶ (A × one) → (A × (exp A two))’
     by metis_tac[pa_hom,compose_hom] >>
   ‘ev A two∶ (A × (exp A two)) → two’ by metis_tac[ev_hom] >>
   ‘to1 (exp X two) ∘ μ ∘ p2 A L∶ (A × L) → one’ by
     metis_tac[compose_hom] >>
   ‘⟨p1 A L,to1 (exp X two) ∘ μ ∘ p2 A L⟩∶ (A × L) → (A × one)’
     by metis_tac[pa_hom] >> 
   ‘(ev A two ∘ ⟨p1 A one,j0 ∘ p2 A one⟩ ∘
         ⟨p1 A L,to1 (exp X two) ∘ μ ∘ p2 A L⟩) =
    (ev A two ∘ ⟨p1 A one,j0 ∘ p2 A one⟩) ∘
         ⟨p1 A L,to1 (exp X two) ∘ μ ∘ p2 A L⟩’
     by metis_tac[compose_assoc] >> 
    ‘ev A two o ⟨p1 A one,j0 ∘ p2 A one⟩ =
     (i1 one one ∘ to1 (A × one))’
     by (simp[Abbr‘j0’] >> metis_tac[ev_of_tp]) >>
    rw[] >>
    ‘to1 (exp X two) ∘ μ ∘ p2 A L∶ (A × L) → one’
     by metis_tac[compose_hom] >>
    ‘⟨p1 A L,to1 (exp X two) ∘ μ ∘ p2 A L⟩∶ (A × L) → (A × one)’
      by metis_tac[pa_hom] >>
    ‘((i1 one one ∘ to1 (A × one)) ∘
         ⟨p1 A L,to1 (exp X two) ∘ μ ∘ p2 A L⟩) =
     i1 one one ∘ to1 (A × one) ∘
         ⟨p1 A L,to1 (exp X two) ∘ μ ∘ p2 A L⟩’
      by metis_tac[compose_assoc] >>
    simp[] >>
    ‘(i1 one one ∘ to1 (A × one) ∘ ⟨p1 A L,to1 (exp X two) ∘ μ ∘ p2 A L⟩) ∘ ⟨x0,t0⟩ =
     i1 one one ∘ to1 (A × one) ∘ ⟨p1 A L,to1 (exp X two) ∘ μ ∘ p2 A L⟩ ∘ ⟨x0,t0⟩’ by metis_tac[compose_assoc_4_3_left] >>
    simp[] >>
    ‘to1 (A × one) ∘ ⟨p1 A L,to1 (exp X two) ∘ μ ∘ p2 A L⟩ ∘
        ⟨x0,t0⟩∶ one → one’ by metis_tac[compose_hom] >>
    ‘to1 (A × one) ∘ ⟨p1 A L,to1 (exp X two) ∘ μ ∘ p2 A L⟩ ∘
        ⟨x0,t0⟩ = id one’ by metis_tac[to1_unique,id1] >>
    metis_tac[idR]) >>
‘∀x. x∶ one → X ∧ (∃xb. xb∶ one → A' ∧ a' o xb = x) ⇒
     ∃t. t∶ one → exp X two ∧
        (∃t0. t0∶ one → L ∧ μ o t0 = t) ∧
        ev X two o ⟨x,t⟩ = i2 one one’
  by
   (rw[] >>
    ‘∃x0. x0∶ one → σ ∧ q o x0 = xb’
     by (‘¬(A'≅ zero)’ by metis_tac[iso_zero_no_mem] >>
         qpat_x_assum ‘is_epi q’ mp_tac >> strip_tac >>
         drule epi_pre_inv  >> strip_tac >>
         first_x_assum (qspecl_then [‘σ’,‘A'’] assume_tac) >>
         ‘∃g. g∶A' → σ ∧ q ∘ g = id A'’ by metis_tac[] >>
         qexists_tac ‘g o xb’ >>
         metis_tac[compose_hom,compose_assoc,idL,id1]) >>
    qexists_tac ‘μ o p2 X L o k o x0’ >>
    ‘μ ∘ p2 X L ∘ k ∘ x0∶ one → exp X two’ by metis_tac[compose_hom]>>
    simp[] >>
    strip_tac (* 2 *)
    >- (qexists_tac ‘p2 X L ∘ k ∘ x0’ >>
       metis_tac[compose_hom])
    >- (‘a' o xb∶ one → X’ by metis_tac[compose_hom] >>
       ‘μ ∘ p2 X L ∘ k ∘ x0∶ one → exp X two’
        by metis_tac[compose_hom] >>
       ‘⟨a' ∘ xb,μ ∘ p2 X L ∘ k ∘ x0⟩∶ one → (X × (exp X two))’
         by metis_tac[pa_hom] >>
       ‘μ o p2 X L∶ (X × L) → exp X two’ by metis_tac[compose_hom]>>
       ‘p2 X L ∘ k ∘ x0∶ one → L’ by metis_tac[compose_hom] >>
       ‘⟨a' ∘ xb, p2 X L ∘ k ∘ x0⟩∶ one → (X × L)’
        by metis_tac[pa_hom] >>
       ‘⟨p1 X L, μ o p2 X L⟩ o ⟨a' ∘ xb, p2 X L ∘ k ∘ x0⟩∶
        one → (X × (exp X two))’ by metis_tac[compose_hom] >> 
       ‘⟨a' ∘ xb,μ ∘ p2 X L ∘ k ∘ x0⟩ =
        ⟨p1 X L, μ o p2 X L⟩ o ⟨a' ∘ xb, p2 X L ∘ k ∘ x0⟩’
         by (irule to_p_eq_applied >>
            qexistsl_tac [‘X’,‘exp X two’,‘one’] >> simp[] >>
            ‘p1 X (exp X two)∶ (X× exp X two) → X ∧
             p2 X (exp X two)∶ (X × exp X two) → exp X two’
              by metis_tac[p1_hom,p2_hom] >>
            ‘p1 X (exp X two) ∘ ⟨p1 X L,μ ∘ p2 X L⟩ ∘
             ⟨a' ∘ xb,p2 X L ∘ k ∘ x0⟩ =
             (p1 X (exp X two) ∘ ⟨p1 X L,μ ∘ p2 X L⟩) ∘
             ⟨a' ∘ xb,p2 X L ∘ k ∘ x0⟩’
              by metis_tac[compose_assoc] >>
            ‘p2 X (exp X two) ∘ ⟨p1 X L,μ ∘ p2 X L⟩ ∘
            ⟨a' ∘ xb,p2 X L ∘ k ∘ x0⟩ =
            (p2 X (exp X two) ∘ ⟨p1 X L,μ ∘ p2 X L⟩) ∘
             ⟨a' ∘ xb,p2 X L ∘ k ∘ x0⟩’
              by metis_tac[compose_assoc] >>
            simp[] >>
            ‘p1 X (exp X two) ∘ ⟨p1 X L,μ ∘ p2 X L⟩ = p1 X L ∧
             p2 X (exp X two) ∘ ⟨p1 X L,μ ∘ p2 X L⟩ = μ o p2 X L ∧
             p1 X (exp X two) ∘ ⟨a' ∘ xb,μ ∘ p2 X L ∘ k ∘ x0⟩ =
             a' o xb ∧
             p2 X (exp X two) ∘ ⟨a' ∘ xb,μ ∘ p2 X L ∘ k ∘ x0⟩ =
             μ o p2 X L o k o x0’
              by metis_tac[p1_of_pa,p2_of_pa] >>
            simp[] >>
            ‘(μ ∘ p2 X L) ∘ ⟨a' ∘ xb,p2 X L ∘ k ∘ x0⟩ =
             μ ∘ p2 X L ∘ ⟨a' ∘ xb,p2 X L ∘ k ∘ x0⟩’
             by metis_tac[compose_assoc] >>
            metis_tac[p1_of_pa,p2_of_pa]) >>
       simp[] >>
       ‘a' o xb = p1 X L o k o x0’ by metis_tac[compose_assoc] >>
       simp[] >>
       ‘k o x0∶ one → (X × L)’ by metis_tac[compose_hom] >>
       ‘p1 X L ∘ k ∘ x0∶ one →  X ∧ p2 X L ∘ k ∘ x0∶ one → L’
        by metis_tac[compose_hom] >>
       ‘⟨p1 X L ∘ k ∘ x0,p2 X L ∘ k ∘ x0⟩∶ one → (X × L)’
        by metis_tac[pa_hom] >> 
       ‘⟨p1 X L ∘ k ∘ x0,p2 X L ∘ k ∘ x0⟩ = k o x0’
        by (irule to_p_eq_applied >>
           qexistsl_tac [‘X’,‘L’,‘one’] >> simp[] >>
           metis_tac[p1_of_pa,p2_of_pa]) >> simp[] >>
       ‘ev X two ∘ ⟨p1 X L,μ ∘ p2 X L⟩ = ub’
        by simp[Abbr‘ub’] >>
       ‘ev X two ∘ ⟨p1 X L,μ ∘ p2 X L⟩ ∘ k ∘ x0 =
        (ev X two ∘ ⟨p1 X L,μ ∘ p2 X L⟩) ∘ k ∘ x0’
        by metis_tac[compose_assoc_4_2_left] >> simp[] >>
       simp[Abbr‘k’] >>
       ‘ub ∘ eqa ub (i2 one one ∘ to1 (X × L)) =
        (i2 one one ∘ to1 (X × L)) ∘
        eqa ub (i2 one one ∘ to1 (X × L))’ by metis_tac[eq_equlity]>>
       ‘ub ∘ eqa ub (i2 one one ∘ to1 (X × L)) ∘ x0 =
        (ub ∘ eqa ub (i2 one one ∘ to1 (X × L))) ∘ x0’
         by metis_tac[compose_assoc] >>
       simp[] >>
       ‘((i2 one one ∘ to1 (X × L)) ∘
       eqa ub (i2 one one ∘ to1 (X × L))) ∘ x0 =
        i2 one one ∘ to1 (X × L) ∘
        eqa ub (i2 one one ∘ to1 (X × L)) ∘ x0’
        by metis_tac[compose_assoc_4_2_left_left] >>
       simp[] >>
       ‘to1 (X × L) ∘ eqa ub (i2 one one ∘ to1 (X × L)) ∘ x0 = id one’
        suffices_by metis_tac[idR] >>
       metis_tac[compose_hom,id1,to1_unique])) >>
‘∀x. x∶ one → X ⇒ ¬((∃x0. x0∶ one → A ∧ a o x0 = x) ∧
                    (∃x0. x0∶ one → A' ∧ a' o x0 = x))’
  by metis_tac[i1_ne_i2] >>
‘∀Q q1 q2. q1∶ Q → A + A' ∧ q2∶ Q → A + A' ∧
           ¬(Q ≅ zero) ∧
           (copa a a' o q1 = copa a a' o q2) ⇒
           ¬(∃q1' q2'. q1'∶ Q → A ∧ q2'∶ Q → A' ∧
             i1 A A' o q1' = q1 ∧
             i2 A A' o q2' = q2)’
 by (rpt strip_tac >>
    ‘∃q0. q0∶ one → Q’ by metis_tac[ax6] >>
    ‘a o q1' o q0∶ one → X ∧
    (∃x0. x0∶one → A ∧ a ∘ x0 = a o q1' o q0) ∧
     ∃x0. x0∶one → A' ∧ a' ∘ x0 = a o q1' o q0’
      suffices_by metis_tac[] >>
    ‘a ∘ q1' ∘ q0∶one → X’ by metis_tac[compose_hom]>>
    rpt strip_tac (* 3 *)
    >- simp[]
    >- (qexists_tac ‘q1' ∘ q0’ >> metis_tac[compose_hom])
    >- (qexists_tac ‘q2' ∘ q0’ >>
       ‘q2' ∘ q0∶one → A'’ by metis_tac[compose_hom] >>
       simp[] >>
       ‘a' ∘ q2' = a ∘ q1'’
        suffices_by metis_tac[compose_assoc] >>
       ‘a = copa a a' o (i1 A A') ∧
        a' = copa a a' o (i2 A A')’
        by metis_tac[i1_of_copa,i2_of_copa] >>
        ‘copa a a' ∘ i1 A A' o q1' =
         copa a a' ∘ i2 A A' o q2'’
         suffices_by metis_tac[compose_assoc] >>
        metis_tac[])) >>
irule is_mono_applied >> qexistsl_tac [‘A+A'’,‘X’] >>
simp[] >> rpt strip_tac >>
irule fun_ext >> qexistsl_tac [‘X'’,‘A + A'’] >> rw[] >>
rename [‘x'∶ one → X'’] >>
‘f o x'∶ one → A + A' ∧ g o x'∶ one → A + A'’
 by metis_tac[compose_hom] >> 
‘∃f0. f0∶ one → A ∧ (i1 A A') o f0 = f o x' ∨
 ∃f0. f0∶ one → A' ∧ (i2 A A') o f0 = f o x'’ by metis_tac[to_copa_fac] (* 2 *)
>- (‘∃g0. g0∶ one → A ∧ (i1 A A') o g0 = g o x' ∨
    ∃g0. g0∶ one → A' ∧ (i2 A A') o g0 = g o x'’ by metis_tac[to_copa_fac] (* 2 *)
    >- (‘i1 A A' ∘ f0 = i1 A A' ∘ g0’ suffices_by metis_tac[] >>
       ‘f0 = g0’ suffices_by metis_tac[] >>
       ‘a o f0 = a o g0’
         suffices_by metis_tac[is_mono_property] >>
       ‘copa a a' o i1 A A' o f0 = copa a a' o i1 A A' o g0’
         suffices_by metis_tac[copa_hom,i1_of_copa,i2_of_copa,compose_assoc]>>
       ‘copa a a' ∘ f o x' = copa a a' ∘ g o x'’ by metis_tac[compose_assoc] >>
       metis_tac[])
    >- (first_x_assum (qspecl_then [‘one’,‘f o x'’,‘g o x'’] assume_tac) >>
       ‘¬(one ≅ zero)’ by metis_tac[one_ne_zero] >>
       ‘copa a a' ∘ f ∘ x' = copa a a' ∘ g ∘ x'’ by metis_tac[compose_assoc]>>
       ‘∃q1' q2'.
            q1'∶one → A ∧ q2'∶one → A' ∧ i1 A A' ∘ q1' = f ∘ x' ∧
            i2 A A' ∘ q2' = g ∘ x'’ suffices_by metis_tac[] >>
       qexistsl_tac [‘f0’,‘g0’] >> metis_tac[]))
>- (‘∃g0. g0∶ one → A ∧ (i1 A A') o g0 = g o x' ∨
    ∃g0. g0∶ one → A' ∧ (i2 A A') o g0 = g o x'’ by metis_tac[to_copa_fac] (* 2 *)
     >- (first_x_assum (qspecl_then [‘one’,‘g o x'’,‘f o x'’] assume_tac) >>
       ‘¬(one ≅ zero)’ by metis_tac[one_ne_zero] >>
       ‘copa a a' ∘ f ∘ x' = copa a a' ∘ g ∘ x'’ by metis_tac[compose_assoc]>>
       ‘∃q1' q2'.
            q1'∶one → A ∧ q2'∶one → A' ∧ i1 A A' ∘ q1' = g ∘ x' ∧
            i2 A A' ∘ q2' = f ∘ x'’ suffices_by metis_tac[] >>
       qexistsl_tac [‘f0'’,‘g0’] >> metis_tac[])
    >- (‘i2 A A' ∘ f0' = i2 A A' ∘ g0'’ suffices_by metis_tac[] >>
       ‘f0' = g0'’ suffices_by metis_tac[] >>
       ‘a' o f0' = a' o g0'’
         suffices_by metis_tac[is_mono_property] >>
       ‘copa a a' o i2 A A' o f0' = copa a a' o i2 A A' o g0'’
         suffices_by metis_tac[copa_hom,i1_of_copa,i2_of_copa,compose_assoc]>>
       metis_tac[compose_assoc] 
       )))
>> irule surj_is_epi >> qexistsl_tac [‘A + A'’,‘X’] >> simp[] >> rw[] >> 
   Cases_on ‘∃b0. b0∶ one → A ∧ a o b0 = b’ (* 2 *)
   >- (fs[] >> qexists_tac ‘i1 A A' o b0’ >>
      ‘i1 A A' ∘ b0∶one → A + A'’ by metis_tac[compose_hom,i1_hom] >>
      simp[] >> 
      ‘copa a a' ∘ i1 A A' ∘ b0 = (copa a a' ∘ i1 A A') ∘ b0’
       by metis_tac[i1_hom,compose_assoc] >>
      ‘(copa a a' ∘ i1 A A') = a’ by metis_tac[i1_of_copa] >>
      metis_tac[])
   >- (‘∃phi.
          phi∶X → one + one ∧ phi ∘ b = i2 one one ∧
          phi ∘ a = i1 one one ∘ to1 A’ by metis_tac[Thm5_lemma_1] >>
      ‘∃b0'. b0'∶ one → A' ∧ a' o b0' = b’
        suffices_by
         (rw[] >> qexists_tac ‘i2 A A' o b0'’ >>
          ‘i2 A A' ∘ b0'∶one → A + A'’ by metis_tac[compose_hom] >>
          ‘copa a a' ∘ i2 A A' ∘ b0' =
           (copa a a' ∘ i2 A A') ∘ b0'’ by metis_tac[compose_assoc] >>
          ‘(copa a a' ∘ i2 A A') = a'’ by metis_tac[i2_of_copa] >>
          metis_tac[]
          ) >>
      ‘p1 X one∶ (X× one) → X’ by metis_tac[p1_hom] >>
      ‘phi o (p1 X one)∶ (X × one) → (one + one)’ by metis_tac[compose_hom] >>
      qabbrev_tac ‘phi0 = tp (phi o p1 X one)’ >>
      ‘phi0∶ one → exp X two’
       by (simp[Abbr‘two’,Abbr‘phi0’] >> metis_tac[tp_hom]) >>
      ‘∃xp. xp∶ one → σ ∧ ⟨p1 X L,μ o p2 X L⟩ o k o xp = ⟨b, phi0⟩’
        by
         (‘a2 o phi0 =
          (j0 ∘ to1 (exp X two)) o phi0’
            by (irule ev_eq_eq >>
               qexistsl_tac [‘A’,‘two’,‘one’] >>
               ‘phi∶X → two’ by metis_tac[Abbr‘two’] >> 
               ‘a2 ∘ phi0∶one → exp A two’ by metis_tac[compose_hom] >>
               ‘(j0 ∘ to1 (exp X two))∶ (exp X two) → exp A two’
                by metis_tac[compose_hom] >>
               ‘(j0 ∘ to1 (exp X two)) ∘ phi0∶one → exp A two’
                by metis_tac[compose_hom] >>
               simp[] >>
               ‘(j0 ∘ to1 (exp X two)) ∘ phi0 =
                j0 ∘ to1 (exp X two) ∘ phi0’ by metis_tac[compose_assoc] >>
               ‘to1 (exp X two) ∘ phi0 = id one’
                 by metis_tac[id1,to1_unique,compose_hom] >>
               ‘((j0 ∘ to1 (exp X two)) ∘ phi0) = j0’ by metis_tac[idR] >>
               ‘ev A two ∘ ⟨p1 A one,((j0 ∘ to1 (exp X two)) ∘ phi0) ∘ p2 A one⟩ =
               ev A two ∘ ⟨p1 A one,j0 ∘ p2 A one⟩’ by metis_tac[] >>
               ‘ev A two ∘ ⟨p1 A one,j0 ∘ p2 A one⟩ =
                (i1 one one ∘ to1 (A × one))’
                by
                 (simp[Abbr‘j0’] >> metis_tac[ev_of_tp]) >>
               rw[] >>
               ‘p1 A one∶ (A × one) → A ∧ p2 A one∶ (A × one)→ one’
                by metis_tac[p1_hom,p2_hom] >>
               ‘(a2 ∘ phi0) ∘ p2 A one∶ (A × one) → exp A two’
                 by metis_tac[compose_hom] >>
               ‘⟨p1 A one,(a2 ∘ phi0) ∘ p2 A one⟩∶
                (A × one) → (A × (exp A two))’ by metis_tac[pa_hom] >>
               ‘a2 o p2 A (exp X two)∶ (A × (exp X two)) → exp A two’
                by metis_tac[compose_hom] >>
               ‘phi0 o p2 A one∶ (A × one) → exp X two’
                by metis_tac[compose_hom] >>
               ‘⟨p1 A (exp X two), a2 o p2 A (exp X two)⟩∶
                (A× (exp X two)) → (A × exp A two)’
                by metis_tac[pa_hom] >>
               ‘⟨p1 A one,phi0 ∘ p2 A one⟩∶ (A × one) → (A × exp X two)’
                 by metis_tac[pa_hom] >> 
               ‘⟨p1 A one,(a2 ∘ phi0) ∘ p2 A one⟩ =
                ⟨p1 A (exp X two), a2 o p2 A (exp X two)⟩ o
                ⟨p1 A one, phi0 o p2 A one⟩’
                 by (irule to_p_eq_applied >>
                    qexistsl_tac [‘A’,‘exp A two’,‘A × one’] >> simp[] >>
                    ‘⟨p1 A (exp X two),a2 ∘ p2 A (exp X two)⟩ ∘
                     ⟨p1 A one,phi0 ∘ p2 A one⟩∶A × one →
                     (A × exp A two)’ by metis_tac[compose_hom] >>
                    simp[] >>
                    ‘p1 A (exp A two) ∘ ⟨p1 A one,(a2 ∘ phi0) ∘ p2 A one⟩ =
                     p1 A one ∧
                     p2 A (exp A two) ∘ ⟨p1 A one,(a2 ∘ phi0) ∘ p2 A one⟩ =
                     (a2 ∘ phi0) ∘ p2 A one’
                     by metis_tac[p1_of_pa,p2_of_pa] >> simp[] >>
                    ‘p1 A (exp A two)∶ (A × (exp A two)) → A’
                     by metis_tac[p1_hom] >>
                    ‘p2 A (exp A two)∶ (A × (exp A two)) → exp A two’
                     by metis_tac[p2_hom] >>
                    ‘p1 A (exp A two) ∘
                     ⟨p1 A (exp X two),a2 ∘ p2 A (exp X two)⟩ ∘
                     ⟨p1 A one,phi0 ∘ p2 A one⟩  =
                     (p1 A (exp A two) ∘
                     ⟨p1 A (exp X two),a2 ∘ p2 A (exp X two)⟩) ∘
                     ⟨p1 A one,phi0 ∘ p2 A one⟩’
                     by metis_tac[compose_assoc] >>
                    ‘p2 A (exp A two) ∘
                     ⟨p1 A (exp X two),a2 ∘ p2 A (exp X two)⟩ ∘
                     ⟨p1 A one,phi0 ∘ p2 A one⟩ =
                     (p2 A (exp A two) ∘
                     ⟨p1 A (exp X two),a2 ∘ p2 A (exp X two)⟩) ∘
                     ⟨p1 A one,phi0 ∘ p2 A one⟩’
                     by metis_tac[compose_assoc] >>
                    simp[] >>
                    ‘(p1 A (exp A two) ∘
                     ⟨p1 A (exp X two),a2 ∘ p2 A (exp X two)⟩) =
                     p1 A (exp X two) ∧
                     (p2 A (exp A two) ∘
                     ⟨p1 A (exp X two),a2 ∘ p2 A (exp X two)⟩) =
                     a2 ∘ p2 A (exp X two)’ by metis_tac[p1_of_pa,p2_of_pa]>>
                    simp[] >>
                    metis_tac[compose_assoc,p1_of_pa,p2_of_pa]) >> rw[] >>
               ‘ev A two∶ (A × (exp A two)) → two’ by metis_tac[ev_hom] >>
               ‘a2 ∘ p2 A (exp X two)∶ (A × (exp X two)) → exp A two’
                by metis_tac[compose_hom] >>
               ‘⟨p1 A (exp X two),a2 ∘ p2 A (exp X two)⟩∶
                (A × (exp X two)) → (A × exp A two)’ by metis_tac[pa_hom] >>
               ‘⟨p1 A one, phi0 o p2 A one⟩∶ (A × one) → (A × (exp X two))’
                 by metis_tac[pa_hom] >> 
               ‘ev A two ∘ ⟨p1 A (exp X two),a2 ∘ p2 A (exp X two)⟩ ∘
                ⟨p1 A one,phi0 ∘ p2 A one⟩ =
                (ev A two o ⟨p1 A (exp X two), a2 o p2 A (exp X two)⟩) o
                ⟨p1 A one, phi0 o p2 A one⟩’ by metis_tac[compose_assoc] >>
               rw[] >>
               ‘ev A two o ⟨p1 A (exp X two), a2 o p2 A (exp X two)⟩ =
                (ev X two ∘ ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩)’
                 by (simp[Abbr‘a2’] >> metis_tac[ev_of_tp]) >>
               rw[] >>
               ‘⟨p1 A one, phi0 o p2 A one⟩∶ (A × one) → (A × (exp X two))’
                by metis_tac[pa_hom] >>
               ‘⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩∶
                (A × (exp X two)) → (X × (exp X two))’
                by metis_tac[pa_hom] >> 
               ‘(ev X two ∘ ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩) o
                ⟨p1 A one, phi0 o p2 A one⟩ =
                ev X two ∘ ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩ o
                ⟨p1 A one, phi0 o p2 A one⟩’ by metis_tac[compose_assoc]>>
               rw[] >>
               (**********************)
               ‘⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩∶
                (A × (exp X two)) → (X × (exp X two))’
                by metis_tac[pa_hom] >>
               ‘⟨p1 A one, phi0 o p2 A one⟩∶ (A × one) → (A × exp X two)’
                by metis_tac[pa_hom] >>
               ‘p2 X one∶ (X × one) → one’ by metis_tac[p2_hom] >>
               ‘phi0 o p2 X one∶ (X × one) → exp X two’
                by metis_tac[compose_hom] >> 
               ‘⟨p1 X one, phi0 o p2 X one⟩∶ (X × one) → (X × exp X two)’
                by metis_tac[pa_hom] >>
               ‘⟨a o p1 A one, p2 A one⟩∶ (A × one) → (X × one)’
                by metis_tac[pa_hom,compose_hom] >>
               ‘⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩ o
                ⟨p1 A one, phi0 o p2 A one⟩∶
                (A × one) → (X × exp X two)’ by metis_tac[compose_hom] >>
               ‘⟨p1 X one, phi0 o p2 X one⟩ o ⟨a o p1 A one, p2 A one⟩∶
                (A × one) → (X × exp X two)’ by metis_tac[compose_hom] >> 
               ‘⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩ o
                ⟨p1 A one, phi0 o p2 A one⟩ =
                ⟨p1 X one, phi0 o p2 X one⟩ o ⟨a o p1 A one, p2 A one⟩’
                by (irule to_p_eq_applied >>
                   qexistsl_tac [‘X’,‘exp X two’,‘A × one’] >>
                   simp[] >>
                   ‘p1 X (exp X two) ∘
                    ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩ ∘
                    ⟨p1 A one,phi0 ∘ p2 A one⟩ =
                    (p1 X (exp X two) ∘
                    ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩) ∘
                    ⟨p1 A one,phi0 ∘ p2 A one⟩’
                    by metis_tac[compose_assoc,p1_hom] >>
                   ‘p2 X (exp X two) ∘
                    ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩ ∘
                    ⟨p1 A one,phi0 ∘ p2 A one⟩ =
                    (p2 X (exp X two) ∘
                    ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩) ∘
                    ⟨p1 A one,phi0 ∘ p2 A one⟩’
                    by metis_tac[compose_assoc,p2_hom] >>
                   ‘p1 X (exp X two) ∘ ⟨p1 X one,phi0 ∘ p2 X one⟩ ∘
                    ⟨a ∘ p1 A one,p2 A one⟩ =
                    (p1 X (exp X two) ∘ ⟨p1 X one,phi0 ∘ p2 X one⟩) ∘
                    ⟨a ∘ p1 A one,p2 A one⟩’
                    by metis_tac[compose_assoc,p1_hom] >>
                   ‘p2 X (exp X two) ∘ ⟨p1 X one,phi0 ∘ p2 X one⟩ ∘
                    ⟨a ∘ p1 A one,p2 A one⟩ =
                    (p2 X (exp X two) ∘ ⟨p1 X one,phi0 ∘ p2 X one⟩) ∘
                    ⟨a ∘ p1 A one,p2 A one⟩’ by metis_tac[compose_assoc,p2_hom] >>
                   simp[] >>
                   ‘p1 X (exp X two) ∘ ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩ =
                    a ∘ p1 A (exp X two)’ by metis_tac[p1_of_pa] >>
                   simp[] >>
                   ‘(p1 X (exp X two) ∘ ⟨p1 X one,phi0 ∘ p2 X one⟩) =
                    p1 X one’ by metis_tac[p1_of_pa] >>
                   ‘(a ∘ p1 A (exp X two)) ∘ ⟨p1 A one,phi0 ∘ p2 A one⟩ =
                    a ∘ p1 A (exp X two) ∘ ⟨p1 A one,phi0 ∘ p2 A one⟩’
                    by metis_tac[compose_assoc] >>
                   ‘p1 A (exp X two) ∘ ⟨p1 A one,phi0 ∘ p2 A one⟩ = p1 A one’
                    by metis_tac[p1_of_pa] >>
                   simp[] >>
                   ‘p1 X one ∘ ⟨a ∘ p1 A one,p2 A one⟩ = a o p1 A one’
                    by metis_tac[p1_of_pa,compose_hom,p1_hom,p2_hom] >>
                   simp[] >>
                   ‘p2 X (exp X two) ∘ ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩ =
                    p2 A (exp X two)’ by metis_tac[p2_of_pa] >>
                   ‘p2 X (exp X two) ∘ ⟨p1 X one,phi0 ∘ p2 X one⟩ =
                    phi0 o p2 X one’ by metis_tac[p2_of_pa] >>
                   simp[] >>
                   ‘(phi0 ∘ p2 X one) ∘ ⟨a ∘ p1 A one,p2 A one⟩ =
                    phi0 ∘ p2 X one ∘ ⟨a ∘ p1 A one,p2 A one⟩’
                    by metis_tac[compose_assoc] >>
                   metis_tac[p2_of_pa,compose_hom])>>
                   (***************)
               rw[] >>
               ‘⟨p1 X one,phi0 ∘ p2 X one⟩∶ (X × one) → (X × (exp X two))’
                by metis_tac[pa_hom,compose_hom,p1_hom,p2_hom] >>
               ‘⟨a ∘ p1 A one,p2 A one⟩∶ (A × one) → (X × one)’
                by metis_tac[compose_hom,pa_hom] >> 
               ‘ev X two ∘ ⟨p1 X one,phi0 ∘ p2 X one⟩ ∘ ⟨a ∘ p1 A one,p2 A one⟩ =
                (ev X two ∘ ⟨p1 X one,phi0 ∘ p2 X one⟩) ∘ ⟨a ∘ p1 A one,p2 A one⟩’
                by metis_tac[compose_assoc] >> rw[] >>
               ‘(ev X two ∘ ⟨p1 X one,phi0 ∘ p2 X one⟩) = (phi ∘ p1 X one)’
                by (simp[Abbr‘phi0’] >> metis_tac[ev_of_tp]) >> rw[] >>
               ‘(phi ∘ p1 X one) ∘ ⟨a ∘ p1 A one,p2 A one⟩ =
                phi ∘ p1 X one ∘ ⟨a ∘ p1 A one,p2 A one⟩’
                by metis_tac[compose_assoc] >> 
               ‘p1 X one ∘ ⟨a ∘ p1 A one,p2 A one⟩ = a ∘ p1 A one’
                by (irule p1_of_pa >> metis_tac[compose_hom]) >>
               rw[] >>
               ‘phi ∘ a ∘ p1 A one = (phi ∘ a) ∘ p1 A one’
                by metis_tac[compose_assoc] >> simp[] >>
               ‘i1 one one ∘ to1 A o p1 A one = i1 one one ∘ to1 (A × one)’
                 suffices_by (strip_tac >> metis_tac[compose_assoc,ax1_1]) >>
               ‘to1 A o p1 A one = to1 (A × one)’
                by metis_tac[compose_assoc,ax1_1,to1_unique,compose_hom] >>
               rw[]) >> 
               
          ‘∃phi0'. phi0'∶ one → L ∧ μ o phi0' = tp (phi o p1 X one)’
           by (simp[Abbr‘L’,Abbr‘μ’] >>
              qexists_tac ‘eq_induce a2 (j0 ∘ to1 (exp X two)) phi0’ >>
              rw[] (* 2 *)
              >- metis_tac[eq_induce_hom]
              >- metis_tac[eq_fac]) >>
          ‘⟨b,phi0'⟩∶ one → (X × L)’ by metis_tac[pa_hom] >> 
          ‘ub o ⟨b,phi0'⟩ = (i2 one one ∘ to1 (X × L)) o ⟨b,phi0'⟩’
            by
             (‘(i2 one one ∘ to1 (X × L)) o ⟨b,phi0'⟩ =
               i2 one one ∘ to1 (X × L) o ⟨b,phi0'⟩’
                by metis_tac[compose_assoc] >>
              ‘to1 (X × L) o ⟨b,phi0'⟩ = id one’
               by metis_tac[id1,to1_unique,compose_hom] >>
              ‘ub ∘ ⟨b,phi0'⟩ = i2 one one’ suffices_by metis_tac[idR] >>
              simp[Abbr‘ub’] >>
              ‘(ev X two ∘ ⟨p1 X L,μ ∘ p2 X L⟩) ∘ ⟨b,phi0'⟩ =
               ev X two ∘ ⟨p1 X L,μ ∘ p2 X L⟩ ∘ ⟨b,phi0'⟩’
                by metis_tac[compose_assoc] >>
              rw[] >>
              ‘⟨p1 X L,μ ∘ p2 X L⟩ ∘ ⟨b,phi0'⟩∶ one → (X× (exp X two))’
                by metis_tac[compose_hom] >>
              ‘⟨b, μ o phi0'⟩∶  one → (X× (exp X two))’ by metis_tac[pa_hom] >>
              ‘⟨p1 X L,μ ∘ p2 X L⟩ ∘ ⟨b,phi0'⟩ =
               ⟨b, μ o phi0'⟩’
                by (irule to_p_eq_applied >>
                   qexistsl_tac [‘X’,‘exp X two’,‘one’] >> simp[] >>
                   ‘p1 X (exp X two) ∘ ⟨b,phi0⟩ = b ∧
                    p2 X (exp X two) ∘ ⟨b,phi0⟩ = phi0’
                    by metis_tac[p1_of_pa,p2_of_pa] >>
                   simp[] >>
                   ‘p1 X (exp X two)∶ (X× (exp X two)) → X ∧
                    p2 X (exp X two)∶ (X× (exp X two)) → (exp X two)’
                    by metis_tac[p1_hom,p2_hom] >>
                   ‘p1 X (exp X two) ∘ ⟨p1 X L,μ ∘ p2 X L⟩ ∘ ⟨b,phi0'⟩ =
                    (p1 X (exp X two) ∘ ⟨p1 X L,μ ∘ p2 X L⟩) ∘ ⟨b,phi0'⟩ ∧
                    p2 X (exp X two) ∘ ⟨p1 X L,μ ∘ p2 X L⟩ ∘ ⟨b,phi0'⟩ =
                    (p2 X (exp X two) ∘ ⟨p1 X L,μ ∘ p2 X L⟩) ∘ ⟨b,phi0'⟩’
                    by metis_tac[compose_assoc] >>
                   simp[] >>
                   ‘(p1 X (exp X two) ∘ ⟨p1 X L,μ ∘ p2 X L⟩) = p1 X L ∧
                    (p2 X (exp X two) ∘ ⟨p1 X L,μ ∘ p2 X L⟩) = μ ∘ p2 X L’
                    by metis_tac[p1_of_pa,p2_of_pa] >>
                   simp[] >>
                   ‘(μ ∘ p2 X L) ∘ ⟨b,phi0'⟩ = μ ∘ p2 X L ∘ ⟨b,phi0'⟩’
                    by metis_tac[compose_assoc] >>
                   ‘p2 X L ∘ ⟨b,phi0'⟩ = phi0'’ by metis_tac[p2_of_pa] >>
                   simp[] >> metis_tac[p1_of_pa])
                >>
              rw[] >>
              ‘ev X two ∘ ⟨b,phi0⟩  = phi o b’ suffices_by metis_tac[] >>
              simp[Abbr‘phi0’] >>
              metis_tac[tp_element_ev])  >>
          ‘∃bp0. bp0∶ one → σ ∧ k o bp0 = ⟨b,phi0'⟩’
           by (simp[Abbr‘σ’,Abbr‘k’] >>
              qexists_tac ‘eq_induce ub (i2 one one ∘ to1 (X × L)) ⟨b,phi0'⟩’ >>
              strip_tac (* 2 *)
              >- metis_tac[eq_induce_hom]
              >-  metis_tac[eq_fac]) >>
          qexists_tac ‘bp0’ >> simp[] >>
          ‘⟨p1 X L,μ ∘ p2 X L⟩ ∘ ⟨b,phi0'⟩∶ one → (X × exp X two)’
           by metis_tac[compose_hom] >>
          ‘⟨b,phi0⟩∶ one → (X × exp X two)’ by metis_tac[pa_hom] >>
          irule to_p_eq_applied >>
          qexistsl_tac [‘X’,‘exp X two’,‘one’] >> simp[] >>
          ‘p1 X (exp X two)∶ (X × (exp X two)) → X’ by metis_tac[p1_hom] >>
          ‘p2 X (exp X two)∶ (X × (exp X two)) → (exp X two)’ by metis_tac[p2_hom] >>
          ‘p1 X (exp X two) ∘ ⟨p1 X L,μ ∘ p2 X L⟩ ∘ ⟨b,phi0'⟩ =
           (p1 X (exp X two) ∘ ⟨p1 X L,μ ∘ p2 X L⟩) ∘ ⟨b,phi0'⟩’
           by metis_tac[compose_assoc] >>
          ‘(p1 X (exp X two) ∘ ⟨p1 X L,μ ∘ p2 X L⟩) ∘ ⟨b,phi0'⟩ =
           (p1 X L) ∘ ⟨b,phi0'⟩’ by metis_tac[p1_of_pa] >>
          ‘(p1 X L) ∘ ⟨b,phi0'⟩ = b’ by metis_tac[p1_of_pa] >>
          ‘p1 X (exp X two) ∘ ⟨b,phi0⟩ = b’ by metis_tac[p1_of_pa] >>
          ‘p2 X (exp X two) ∘ ⟨b,phi0⟩ = phi0’ by metis_tac[p2_of_pa] >>
          ‘p2 X (exp X two) ∘ ⟨p1 X L,μ ∘ p2 X L⟩ ∘ ⟨b,phi0'⟩ = phi0’
            suffices_by metis_tac[] >>
          ‘p2 X (exp X two) ∘ ⟨p1 X L,μ ∘ p2 X L⟩ ∘ ⟨b,phi0'⟩ =
           (p2 X (exp X two) ∘ ⟨p1 X L,μ ∘ p2 X L⟩) ∘ ⟨b,phi0'⟩’
            by metis_tac[compose_assoc] >>
          ‘(p2 X (exp X two) ∘ ⟨p1 X L,μ ∘ p2 X L⟩) = μ ∘ p2 X L’
            by metis_tac[p2_of_pa] >>
          rw[] >>
          ‘(μ ∘ p2 X L) ∘ ⟨b,phi0'⟩ = μ ∘ p2 X L ∘ ⟨b,phi0'⟩’
            by metis_tac[compose_assoc] >>
          ‘μ o phi0' = phi0’ suffices_by metis_tac[p2_of_pa] >>
          metis_tac[Abbr‘phi0’]) >>
      qexists_tac ‘q o xp’ >>
      ‘q o xp∶ one → A'’ by metis_tac[compose_hom] >> simp[] >>
      ‘p1 X (exp X two) o ⟨p1 X L, μ o p2 X L⟩ = p1 X L’
        by metis_tac[p1_of_pa] >>
      ‘(p1 X (exp X two)) o ⟨b,phi0⟩ = b’ by metis_tac[p1_of_pa] >>
      ‘a' ∘ q ∘ xp = (p1 X (exp X two)) o ⟨b,phi0⟩’ suffices_by metis_tac[]>>
      ‘a' ∘ q ∘ xp  = (a' ∘ q) ∘ xp’ by metis_tac[compose_assoc] >>
      ‘p1 X L ∘ k o xp =
       (p1 X (exp X two)) o ⟨b,phi0⟩’ suffices_by metis_tac[compose_assoc] >>
      ‘(p1 X (exp X two) o ⟨p1 X L, μ o p2 X L⟩) o k o xp
        = (p1 X (exp X two)) o ⟨b,phi0⟩’
        suffices_by metis_tac[] >>
      ‘(p1 X (exp X two) ∘ ⟨p1 X L,μ ∘ p2 X L⟩) ∘ k ∘ xp =
       p1 X (exp X two) ∘ ⟨p1 X L,μ ∘ p2 X L⟩ ∘ k ∘ xp’
        by (irule compose_assoc_4_2_left >>
           qexists_tac ‘X × (exp X two)’ >>
           qexists_tac ‘X’ >>
           qexists_tac ‘one’ >>
           qexists_tac ‘σ’ >>
           qexists_tac ‘X × L’ >> rw[]) >>
      rw[])
QED               
             

                    

Theorem char_exists:
∀a. is_mono a ⇒ ∃phi. phi∶ cod a → (one + one) ∧
    ∀x. x∶ one → cod a ⇒ ((∃x0. x0∶ one → dom a ∧ a o x0 = x) ⇔
                         phi o x = i2 one one)
Proof
rw[] >>
drule Thm5 >> rw[] >>
qabbrev_tac ‘A = dom a’ >> qabbrev_tac ‘X = cod a’ >>
‘a∶ A → X’ by metis_tac[hom_def] >>
first_x_assum drule >> rw[] >>
‘copa a a'∶ A + A' → X’ by metis_tac[copa_hom] >>
drule is_iso_thm >> rw[] >>
‘i2 one one o to1 A∶ A → one + one’
 by metis_tac[i2_hom,to1_hom,compose_hom] >>
‘i1 one one o to1 A'∶ A' → one + one’
 by metis_tac[i1_hom,to1_hom,compose_hom] >>
‘copa (i2 one one o to1 A) (i1 one one o to1 A')∶ A + A' → one + one’
 by metis_tac[copa_hom] >>
rename [‘ copa a a' ∘ f = id X’] >>
‘copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') o f∶ X → one + one’
 by metis_tac[compose_hom] >>
qexists_tac ‘copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') o f’ >>
simp[] >> rw[] >>
rw[EQ_IMP_THM] (*2  *)
>- (‘copa a a' o i1 A A' = a’ by metis_tac[i1_of_copa] >>
   ‘f o copa a a' o i1 A A' = (f o copa a a') o i1 A A'’
    by metis_tac[i1_hom,compose_assoc] >>
   ‘f o a = i1 A A'’ by metis_tac[idL,i1_hom] >>
   ‘(copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ f) ∘ a ∘ x0 =
    copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ (f ∘ a) ∘ x0’
    by metis_tac[compose_assoc_4_2_left_middle] >>
   simp[] >>
   ‘copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ i1 A A' ∘ x0 =
    (copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ i1 A A') ∘ x0’
    by metis_tac[i1_hom,compose_assoc] >>
   simp[] >>
   ‘copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ i1 A A' =
    (i2 one one ∘ to1 A)’ by metis_tac[i1_of_copa] >>
   simp[] >>
   ‘(i2 one one ∘ to1 A) ∘ x0 = i2 one one ∘ to1 A ∘ x0’
    by metis_tac[compose_assoc,to1_hom,i2_hom] >>
   ‘to1 A o x0 = id one’
    by metis_tac[compose_hom,to1_hom,id1,to1_unique] >>
   simp[] >> metis_tac[i2_hom,idR])
>- (‘f o x∶ one → A + A'’ by metis_tac[compose_hom] >>
   drule to_copa_fac >> rw[] (* 2 *)
   >- (‘a = copa a a' o i1 A A'’ by metis_tac[i1_of_copa] >>
      qexists_tac ‘x0’ >> simp[] >>
      ‘copa a a' ∘ i1 A A' o x0 = x’
       suffices_by metis_tac[i1_hom,compose_assoc] >>
      simp[] >>
      metis_tac[idL,compose_assoc])
   >- (‘(copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ f) ∘ x =
       i1 one one’ suffices_by metis_tac[i1_ne_i2] >>
      ‘(copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ f) ∘ x =
       copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ f ∘ x’
       by metis_tac[compose_assoc] >>
      ‘copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ i2 A A' ∘ x0' = i1 one one’ suffices_by metis_tac[] >>
      ‘copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ i2 A A' ∘ x0' = (copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ i2 A A') ∘ x0'’
       by metis_tac[i2_hom,compose_assoc] >>
      simp[] >>
      ‘copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ i2 A A' =
       i1 one one o to1 A'’ by metis_tac[i2_of_copa] >>
      simp[] >>
      ‘(i1 one one ∘ to1 A') ∘ x0' = i1 one one ∘ to1 A' ∘ x0'’
       by metis_tac[i1_hom,compose_assoc,to1_hom] >>
      simp[] >>
      ‘to1 A' ∘ x0' = id one’
       by metis_tac[to1_hom,compose_hom,id1,to1_unique] >>
      metis_tac[idR,i1_hom]))
QED
     

Theorem char_exists_thm = SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM] char_exists        

val char_def = new_specification ("char_def",["char"],char_exists_thm)
(*
Theorem sing_exists:
∀A. ∃s. s∶ A → exp A 2 ∧
    ∀x y. x∶ one → A ∧ y∶ one → A ⇒
    (∃y0. y0∶ one → eqo () ((i2 one one) o (to1 A))) ⇔
    y = x
        *)


Theorem char_thm:
∀a A X.
    is_mono a ∧ a∶ A → X ⇒
         char a∶ X → one + one ∧
         ∀x.
             x∶one → X ⇒
             ((∃x0. x0∶one → A ∧ a ∘ x0 = x) ⇔ char a ∘ x = i2 one one)
Proof
strip_tac >> strip_tac >> strip_tac >> strip_tac >>
fs[hom_def] >> metis_tac[char_def,hom_def]
QED

        (*

Definition n2a_def:
n2a f = 

(*n2a sends a 1 --> 2^A  to transpose, a2n other direction*)

  ev A (one + one) o ⟨p1 A one, hb o tp (psi o p2 one R)⟩
*)

val _ = overload_on("two", “one + one”);        
           
Theorem mem_of_name_eqa:
∀psi R r. psi∶ R → two ∧ r∶ one → R ⇒
               (psi o r = i2 one one ⇔
                ∃r'. r'∶ one → eqo (ev R two) (i2 one one o to1 (R × exp R two)) ∧
                    eqa (ev R two) (i2 one one o to1 (R × exp R two)) o r' = ⟨r, tp (psi ∘ p1 R one)⟩)
Proof
rw[] >>
‘ev R two∶ (R × (exp R two)) → two’ by metis_tac[ev_hom] >>
‘to1 (R × exp R two)∶ (R × (exp R two)) → one’
 by metis_tac[to1_hom] >>
‘i2 one one∶ one → two’ by metis_tac[i2_hom] >>
‘p1 R one∶ (R × one) → R’ by metis_tac[p1_hom] >>
‘psi o p1 R one∶ (R × one) → two’ by metis_tac[compose_hom] >>
‘tp (psi ∘ p1 R one)∶ one → exp R two’ by metis_tac[tp_hom] >>
‘⟨r,tp (psi ∘ p1 R one)⟩∶one → (R × (exp R two))’
 by metis_tac[pa_hom] >> 
‘(i2 one one ∘ to1 (R × exp R two))∶ (R × (exp R two)) → two’
 by metis_tac[compose_hom] >> 
‘(∃r'.
                 r'∶one → eqo (ev R two) (i2 one one ∘ to1 (R × exp R two)) ∧
                 eqa (ev R two) (i2 one one ∘ to1 (R × exp R two)) ∘ r' =
                 ⟨r,tp (psi ∘ p1 R one)⟩) ⇔
   (ev R two) o ⟨r,tp (psi ∘ p1 R one)⟩ = (i2 one one ∘ to1 (R × exp R two)) o ⟨r,tp (psi ∘ p1 R one)⟩’
  by (irule fac_through_eq_iff >> metis_tac[]) >>
rw[] >>
‘(i2 one one ∘ to1 (R × exp R two)) ∘ ⟨r,tp (psi ∘ p1 R one)⟩ =
 i2 one one ∘ to1 (R × exp R two) ∘ ⟨r,tp (psi ∘ p1 R one)⟩’
 by metis_tac[compose_assoc] >>
‘to1 (R × exp R two) ∘ ⟨r,tp (psi ∘ p1 R one)⟩ = id one’
 by (irule to1_unique >> metis_tac[id1,compose_hom]) >>
simp[] >>
‘i2 one one ∘ id one = i2 one one’ by metis_tac[idR] >>
simp[] >> metis_tac[tp_element_ev]
QED

Theorem compose_with_id_to1:
∀x A. x∶ one → A ⇒ ⟨id A,to1 A⟩ ∘ x = ⟨x, id one⟩
Proof
rw[] >>
‘id A∶ A → A ∧ to1 A∶ A → one’ by metis_tac[to1_hom,id1] >>
‘⟨id A,to1 A⟩∶ A → (A × one)’ by metis_tac[pa_hom] >>
‘⟨id A,to1 A⟩ ∘ x∶ one → (A × one)’ by metis_tac[compose_hom] >>
‘id one∶ one → one’ by metis_tac[id1] >>
‘⟨x,id one⟩∶ one → (A × one)’ by metis_tac[pa_hom] >>
irule to_p_eq_applied >>
qexistsl_tac [‘A’,‘one’,‘one’] >> simp[] >>
‘p1 A one ∘ ⟨id A,to1 A⟩ o x = (p1 A one ∘ ⟨id A,to1 A⟩) o x ∧
 p2 A one ∘ ⟨id A,to1 A⟩ o x = (p2 A one ∘ ⟨id A,to1 A⟩) o x’
 by metis_tac[p1_hom,p2_hom,compose_assoc] >>
simp[] >>
‘(p1 A one ∘ ⟨id A,to1 A⟩) = id A ∧
 p1 A one o ⟨x, id one⟩ = x’ by metis_tac[p1_of_pa] >>
‘(p2 A one ∘ ⟨id A,to1 A⟩) = to1 A ∧
 p2 A one o ⟨x, id one⟩ = id one’ by metis_tac[p2_of_pa] >>
simp[] >> metis_tac[to1_unique,idL,compose_hom]
QED


Theorem ev_compose_split:
∀A B X Y f g. g∶ X → exp A Y ∧ f∶ B → X  ⇒
          (ev A Y) o ⟨p1 A B, g o f o p2 A B⟩ = 
          ((ev A Y) o ⟨p1 A X, g o p2 A X⟩) o
           ⟨p1 A B,f o p2 A B⟩
Proof
rw[] >>
‘ev A Y∶ (A × exp A Y) → Y’ by metis_tac[ev_hom] >>
‘p1 A X∶ (A × X) → A ∧ p2 A X∶ (A × X) → X ∧
 p1 A B∶ (A × B) → A ∧ p2 A B∶ (A × B) → B’
 by metis_tac[p1_hom,p2_hom] >>
‘g o p2 A X∶ (A × X) → exp A Y ∧ f o p2 A B∶ (A × B) → X’
 by metis_tac[compose_hom] >>
‘⟨p1 A B,f ∘ p2 A B⟩∶ (A × B) → (A × X)’ by metis_tac[pa_hom] >>
‘⟨p1 A X,g ∘ p2 A X⟩∶ (A × X) → (A × exp A Y)’
 by metis_tac[pa_hom] >>
‘(ev A Y ∘ ⟨p1 A X,g ∘ p2 A X⟩) ∘ ⟨p1 A B,f ∘ p2 A B⟩ =
 ev A Y ∘ ⟨p1 A X,g ∘ p2 A X⟩ ∘ ⟨p1 A B,f ∘ p2 A B⟩’
 by metis_tac[compose_assoc,pa_hom] >>
‘⟨p1 A B,g ∘ f ∘ p2 A B⟩ =
 ⟨p1 A X,g ∘ p2 A X⟩ ∘ ⟨p1 A B,f ∘ p2 A B⟩’
 suffices_by metis_tac[] >>
irule parallel_p_one_side >> metis_tac[]
QED

Theorem two_steps_compose_combine:
∀A X Y f g. f∶ X → A ∧ g∶ X → Y ⇒
       ⟨p1 A X,g o p2 A X⟩ o ⟨f, id X⟩ = ⟨f,g⟩
Proof
rw[] >>
‘p1 A X∶ (A × X) → A ∧ p2 A X∶ (A × X) → X ∧ id X∶ X → X’
 by metis_tac[p1_hom,p2_hom,id1] >>
‘g o p2 A X∶ (A × X) → Y’ by metis_tac[compose_hom] >>
irule to_p_eq_applied >> qexistsl_tac [‘A’,‘Y’,‘X’] >>
‘⟨p1 A X,g ∘ p2 A X⟩∶ (A × X) → (A × Y)’ by metis_tac[pa_hom] >>
‘⟨f,id X⟩∶ X → (A × X)’ by metis_tac[pa_hom] >>
‘⟨f,g⟩∶ X → (A × Y)’ by metis_tac[pa_hom] >>
‘p1 A Y ∘ ⟨p1 A X,g ∘ p2 A X⟩ ∘ ⟨f,id X⟩ =
 (p1 A Y ∘ ⟨p1 A X,g ∘ p2 A X⟩) ∘ ⟨f,id X⟩’
 by metis_tac[p1_hom,compose_assoc] >>
‘p2 A Y ∘ ⟨p1 A X,g ∘ p2 A X⟩ ∘ ⟨f,id X⟩ =
 (p2 A Y ∘ ⟨p1 A X,g ∘ p2 A X⟩) ∘ ⟨f,id X⟩’
 by metis_tac[p2_hom,compose_assoc] >>
‘(p1 A Y ∘ ⟨p1 A X,g ∘ p2 A X⟩) = p1 A X’
 by metis_tac[p1_of_pa] >>
‘(p2 A Y ∘ ⟨p1 A X,g ∘ p2 A X⟩) = g ∘ p2 A X’
 by metis_tac[p2_of_pa] >>
simp[] >>
‘(g ∘ p2 A X) ∘ ⟨f,id X⟩ = g ∘ p2 A X ∘ ⟨f,id X⟩’
 by metis_tac[compose_assoc] >>
simp[] >>
‘p2 A X ∘ ⟨f,id X⟩ = id X’ by metis_tac[p2_of_pa] >>
simp[] >> metis_tac[p1_of_pa,p2_of_pa,idR,compose_hom]
QED
        
        
Theorem compose_partial_ev:
∀A X Y x psi ϕ.
  x∶ one → A ∧ psi∶ X → Y ∧ ϕ∶ (A × exp X Y) → Y ⇒ 
             ϕ ∘ ⟨x,tp (psi ∘ p1 X one)⟩ =
             ev A Y ∘ ⟨p1 A one,tp ϕ ∘ tp (psi ∘ p1 X one) o p2 A one⟩ ∘
             ⟨id A,to1 A⟩ ∘ x
Proof
rw[] >>
‘tp ϕ∶ exp X Y → exp A Y’ by metis_tac[tp_hom] >>
drule ev_compose_split  >> strip_tac >>
‘p1 X one∶ (X × one) → X’ by metis_tac[p1_hom] >>
‘psi o p1 X one∶ (X × one) → Y’ by metis_tac[compose_hom] >>
‘tp (psi o p1 X one)∶ one → exp X Y’ by metis_tac[tp_hom] >>
first_x_assum drule >> rw[] >>
‘⟨id A,to1 A⟩ ∘ x =  ⟨x, id one⟩’
 by metis_tac[compose_with_id_to1] >>
simp[] >>
‘p1 A one∶ (A × one) → A ∧ p2 A one∶ (A × one) → one’
 by metis_tac[p1_hom,p2_hom] >>
‘tp ϕ ∘ tp (psi ∘ p1 X one) ∘ p2 A one∶ (A × one) → exp A Y’
 by metis_tac[compose_hom] >>
‘⟨p1 A one,tp ϕ ∘ tp (psi ∘ p1 X one) ∘ p2 A one⟩∶
 (A × one) → (A × exp A Y)’ by metis_tac[pa_hom] >>
‘⟨x,id one⟩∶ one → (A × one)’ by metis_tac[id1,pa_hom] >>
‘ev A Y∶ (A × exp A Y) → Y’ by metis_tac[ev_hom] >>
‘ev A Y ∘ ⟨p1 A one,tp ϕ ∘ tp (psi ∘ p1 X one) ∘ p2 A one⟩ ∘
        ⟨x,id one⟩ =
 (ev A Y ∘ ⟨p1 A one,tp ϕ ∘ tp (psi ∘ p1 X one) ∘ p2 A one⟩) ∘
        ⟨x,id one⟩’ by metis_tac[compose_assoc] >>
simp[] >>
‘ev A Y ∘ ⟨p1 A (exp X Y),tp ϕ ∘ p2 A (exp X Y)⟩ = ϕ’
 by metis_tac[ev_of_tp] >>
simp[] >>
‘tp (psi ∘ p1 X one) ∘ p2 A one∶ (A × one) → exp X Y’
 by metis_tac[compose_hom] >>
‘(ϕ ∘ ⟨p1 A one,tp (psi ∘ p1 X one) ∘ p2 A one⟩) ∘ ⟨x,id one⟩ =
  ϕ ∘ ⟨p1 A one,tp (psi ∘ p1 X one) ∘ p2 A one⟩ ∘ ⟨x,id one⟩’
  by metis_tac[compose_assoc,pa_hom] >>
simp[] >>
‘⟨x,tp (psi ∘ p1 X one)⟩ =
 ⟨p1 A one,tp (psi ∘ p1 X one) ∘ p2 A one⟩ ∘ ⟨x,id one⟩’
 suffices_by metis_tac[] >>
metis_tac[two_steps_compose_combine]
QED
        




Theorem is_trans_thm:
∀f0 f1 R A. f0∶ R → A ∧ f1∶ R → A ⇒
         (is_trans f0 f1 ⇔
         ∀X h0 h1.
             h0∶X → R ∧ h1∶X → R ∧ f1 ∘ h0 = f0 ∘ h1 ⇒
             ∃u. u∶X → R ∧ f0 ∘ u = f0 ∘ h0 ∧ f1 ∘ u = f1 ∘ h1)
Proof
rw[] >>
metis_tac[is_trans_def,hom_def]
QED



Theorem is_refl_thm:
∀f0 f1 R A. f0∶ R → A ∧ f1∶ R → A ⇒
         (is_refl f0 f1 ⇔
         ∃d. d∶ A → R ∧ f0 ∘ d = id A ∧ f1 ∘ d = id A)
Proof
rw[] >>
metis_tac[is_refl_def,hom_def]
QED

val is_refl_thm_l2r =
      is_refl_thm
      |> SPEC_ALL |> SPEC_ALL |> SPEC_ALL |> SPEC_ALL
      |> UNDISCH |> EQ_IMP_RULE |> #1 |> UNDISCH
      |> DISCH “f0∶R → A ∧ f1∶R → A” |> DISCH_ALL
      |> Q.GEN ‘R’ |> Q.GEN ‘A’ |> Q.GEN ‘f0’ |> Q.GEN ‘f1’  
            
Theorem is_refl_equiv_to_itself:
∀f0 f1 a A R.
 is_refl f0 f1 ∧ f0∶ R → A ∧ f1∶ R → A ∧ a∶ one → A ⇒
 ∃r. r∶ one → R ∧ f0 o r = a ∧ f1 o r = a
Proof
rw[] >> drule is_refl_thm_l2r >> rw[] >>
first_x_assum drule_all >> rw[] >>
qexists_tac ‘d o a’ >>
‘d o a∶ one → R’ by metis_tac[compose_hom] >>
metis_tac[compose_assoc,idL]
QED

   
Theorem equiv_to_same_element:
∀a0 a1 f0 f1 R A.
 a0∶ one → A ∧ a1∶ one → A ∧ f0∶ R → A ∧ f1∶ R → A ∧
 is_refl f0 f1 ∧
  (∀a'.
             a'∶one → A ⇒
             ((∃r. r∶one → R ∧ f0 ∘ r = a0 ∧ f1 ∘ r = a') ⇔
              ∃r. r∶one → R ∧ f0 ∘ r = a1 ∧ f1 ∘ r = a')) ⇒
  ∃r. r∶ one → R ∧ f0 o r = a0 ∧ f1 o r = a1
Proof
rw[] >> metis_tac[is_refl_equiv_to_itself]
QED



Theorem symm_trans_rel_lemma:
∀f0 f1 a R A r.
 is_symm f0 f1 ∧ is_trans f0 f1 ∧
 f0∶ R → A ∧ f1∶ R → A ∧ a∶ one → A ∧ r∶ one → R ⇒
       ((∃r'. r'∶one → R ∧ f0 ∘ r' = f0 ∘ r ∧ f1 ∘ r' = a) ⇔
        (∃r''. r''∶one → R ∧ f0 ∘ r'' = f1 ∘ r ∧ f1 ∘ r'' = a))
Proof
rw[EQ_IMP_THM] (* 2 *)
>- (‘∃t. t∶ R → R ∧ f0 o t = f1 ∧ f1 o t = f0’
     by metis_tac[is_symm_def,hom_def] >>
   ‘f1 o t ∘ r' = f0 ∘ r’
    by metis_tac[compose_assoc] >>
   ‘(is_trans f0 f1 ⇔
          ∀X h0 h1.
              h0∶X → R ∧ h1∶X → R ∧ f1 ∘ h0 = f0 ∘ h1 ⇒
              ∃u. u∶X → R ∧ f0 ∘ u = f0 ∘ h0 ∧ f1 ∘ u = f1 ∘ h1)’ by (irule is_trans_thm >> metis_tac[]) >>  rfs[] >>
   ‘t o r'∶ one → R’ by metis_tac[compose_hom] >>
  first_x_assum (qspecl_then [‘one’,‘t o r'’,‘r’] assume_tac)>>
  ‘∃u. u∶one → R ∧ f0 ∘ u = f0 ∘ t ∘ r' ∧ f1 ∘ u = f1 ∘ r’
   by metis_tac[] >>
  qexists_tac ‘t o u’ >>
  ‘t o u∶ one → R’ by metis_tac[compose_hom] >>
  metis_tac[compose_assoc])
>- (‘(is_trans f0 f1 ⇔
          ∀X h0 h1.
              h0∶X → R ∧ h1∶X → R ∧ f1 ∘ h0 = f0 ∘ h1 ⇒
              ∃u. u∶X → R ∧ f0 ∘ u = f0 ∘ h0 ∧ f1 ∘ u = f1 ∘ h1)’ by (irule is_trans_thm >> metis_tac[]) >>  rfs[])
QED




Theorem to_p_with_1:
∀A a. a∶ one → (A × one) ⇒ ∃a0. a0∶one → A ∧
      a = ⟨a0, id one⟩
Proof
rw[] >> qexists_tac ‘p1 A one o a’ >>
‘p1 A one o a∶ one → A’ by metis_tac[compose_hom,p1_hom] >>
‘⟨p1 A one o a, id one⟩∶ one → (A × one)’ by metis_tac[id1,pa_hom] >>
rw[] >> irule to_p_eq_applied >> qexistsl_tac [‘A’,‘one’,‘one’] >>
simp[] >>
‘p2 A one o a∶ one → one’ by metis_tac[p2_hom,compose_hom] >>
‘p2 A one o a = id one’ by metis_tac[id1,to1_unique] >>
‘p2 A one ∘ ⟨p1 A one ∘ a,id one⟩ = id one’
 by metis_tac[p2_of_pa,id1] >>
simp[] >>
metis_tac[id1,p1_of_pa]
QED

Theorem one_to_two_cases:
∀f. f∶ one → two ⇒ f = i1 one one ∨ f = i2 one one
Proof
rw[] >> drule to_copa_fac >> rw[] (* 2 *)
>- (‘x0 = id one’ by metis_tac[id1,to1_unique] >> simp[] >>
   metis_tac[i1_hom,idR]) >>
‘x0' = id one’ by metis_tac[id1,to1_unique] >> simp[] >>
metis_tac[i2_hom,idR] 
QED
   
Theorem one_to_two_eq:
∀f g. f∶ one → two ∧ g∶ one → two ∧
      (f = i2 one one ⇔ g = i2 one one) ⇒ f = g
Proof
rw[] >> Cases_on ‘f = i2 one one’
>- metis_tac[]
>- (‘g ≠ i2 one one’ by metis_tac[] >>
   metis_tac[one_to_two_cases])
QED
    
        
Theorem fac_char:
∀m A X. is_mono m ∧ m∶ A → X ⇒
        ∀P p f. p∶ P → X ∧ f∶ P → A ∧ m o f = p ⇒
                char m o p = (i2 one one) ∘ to1 P
Proof
rw[] >> drule char_thm >> rw[] >>
first_x_assum drule >> rw[] >>
‘char m ∘ m ∘ f∶ P → two ∧ i2 one one o to1 P∶ P → two’
 by metis_tac[compose_hom,i2_hom,to1_hom] >>
irule fun_ext >> qexistsl_tac [‘P’,‘two’] >> simp[] >>
rw[] >>
‘(char m ∘ m ∘ f) ∘ a = char m ∘ m ∘ f ∘ a’
 by (irule compose_assoc_4_3_left >> metis_tac[]) >>
rw[] >>
‘m o f o a∶ one → X’ by metis_tac[compose_hom] >>
first_x_assum drule >> rw[] >>
‘f o a∶ one → A’ by metis_tac[compose_hom] >>
‘(i2 one one ∘ to1 P) ∘ a = i2 one one ∘ to1 P ∘ a’
 by metis_tac[compose_assoc,i2_hom,to1_hom] >>
simp[] >>
‘to1 P o a = id one’
 by metis_tac[to1_hom,compose_hom,id1,to1_unique] >>
simp[] >> metis_tac[i2_hom,idR]
QED

Theorem fac_char_via_any_map:
∀f A B M m e b. is_epi e ∧ is_mono m ∧ f = m o e ∧
              f∶ A → B ∧ e∶ A → M ∧ m∶ M → B ∧
              b∶ one → B ∧ (char m) o b = i2 one one ⇒
              ∃a. a∶ one → A ∧ f o a = b
Proof
rw[] >> drule epi_has_section >> rw[] >>
first_x_assum drule >> rw[] >>
drule char_thm >> rw[] >> first_x_assum drule >> rw[] >>
first_x_assum (qspec_then ‘b’ assume_tac) >> rfs[] >>
qexists_tac ‘s' o x0’ >>
‘s' o x0 ∶ one → A’ by metis_tac[compose_hom] >> simp[] >>
‘(m ∘ e) ∘ s' ∘ x0 = m ∘ (e ∘ s') ∘ x0’
 by metis_tac[compose_assoc_4_2_left_middle] >>
metis_tac[idL,idR]
QED


        
val _ = export_theory();


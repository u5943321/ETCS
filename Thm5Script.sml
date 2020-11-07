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
reverse (strip_tac) (* 2 *) >-
‘(j0 o (to1 (exp X two))) o μ = a2 o μ’
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
    ‘∃x0. x0∶ one → σ ∧ q o x0 = xb’ by cheat >>
    qexists_tac ‘μ o p2 X L o k o x0’ >>
    ‘μ ∘ p2 X L ∘ k ∘ x0∶ one → exp X two’ by metis_tac[compose_hom]>>
    simp[] >>
    strip_tac (* 2 *)
    >- (qexists_tac ‘p2 X L ∘ k ∘ x0’ >>
       metis_tac[compose_hom])
    >- ‘⟨a' ∘ xb,μ ∘ p2 X L ∘ k ∘ x0⟩ =
        ⟨p1 X L, μ o p2 X L⟩ o ⟨a' ∘ xb, p2 X L ∘ k ∘ x0⟩’
         by cheat >> simp[] >>
       ‘a' o xb = p1 X L o k o x0’ by cheat >> simp[] >> 
       ‘⟨p1 X L ∘ k ∘ x0,p2 X L ∘ k ∘ x0⟩ = k o x0’
        by
         cheat >> simp[] >>
       ‘ev X two ∘ ⟨p1 X L,μ ∘ p2 X L⟩ = ub’
        by simp[Abbr‘ub’] >>
       ‘ev X two ∘ ⟨p1 X L,μ ∘ p2 X L⟩ ∘ k ∘ x0 =
        (ev X two ∘ ⟨p1 X L,μ ∘ p2 X L⟩) ∘ k ∘ x0’
        by cheat >> simp[] >>
       simp[Abbr‘k’] >>
       ‘ub ∘ eqa ub (i2 one one ∘ to1 (X × L)) =
        (i2 one one ∘ to1 (X × L)) ∘
        eqa ub (i2 one one ∘ to1 (X × L))’ by metis_tac[eq_equlity]>>
       cheat
       
       
    
    )
  cheat >>
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
    ∃g0. g0∶ one → A' ∧ (i2 A A') o g0 = g o x'’ by metis_tac[to_copa_fac] (* 2 *)     >- (first_x_assum (qspecl_then [‘one’,‘g o x'’,‘f o x'’] assume_tac) >>
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
       ))
>- irule surj_is_epi >> qexistsl_tac [‘A + A'’,‘X’] >> simp[] >> rw[] >>
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
               ‘⟨p1 A one,(a2 ∘ phi0) ∘ p2 A one⟩ =
                ⟨p1 A one, a2 o p2 A (exp X two)⟩ o ⟨p1 A one, phi0 o p2 A one⟩’
                 by cheat >> rw[]
               ‘ev A two ∘ ⟨p1 A one,a2 ∘ p2 A (exp X two)⟩ ∘
                ⟨p1 A one,phi0 ∘ p2 A one⟩ =
                (ev A two o ⟨p1 A one, a2 o p2 A (exp X two)⟩) o
                ⟨p1 A one, phi0 o p2 A one⟩’ by cheat >> rw[]
               ‘ev A two o ⟨p1 A one, a2 o p2 A (exp X two)⟩ =
                (ev X two ∘ ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩)’ by cheat >>
               rw[] >> 
               ‘(ev X two ∘ ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩) o
                ⟨p1 A one, phi0 o p2 A one⟩ =
                ev X two ∘ ⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩ o
                ⟨p1 A one, phi0 o p2 A one⟩’ by cheat >> rw[] >> 
               ‘⟨a ∘ p1 A (exp X two),p2 A (exp X two)⟩ o
                ⟨p1 A one, phi0 o p2 A one⟩ =
                ⟨p1 X one, phi0 o p2 X one⟩ o ⟨a o p1 A one, p2 A one⟩’
                by cheat >>
               rw[] >>
               ‘ev X two ∘ ⟨p1 X one,phi0 ∘ p2 X one⟩ ∘ ⟨a ∘ p1 A one,p2 A one⟩ =
                (ev X two ∘ ⟨p1 X one,phi0 ∘ p2 X one⟩) ∘ ⟨a ∘ p1 A one,p2 A one⟩’
                 by cheat >> rw[] >>
               ‘(ev X two ∘ ⟨p1 X one,phi0 ∘ p2 X one⟩) =
                (phi ∘ p1 X one)’ by cheat >> rw[] >>
               ‘(phi ∘ p1 X one) ∘ ⟨a ∘ p1 A one,p2 A one⟩ =
                phi ∘ p1 X one ∘ ⟨a ∘ p1 A one,p2 A one⟩’ by cheat >> 
               ‘p1 X one ∘ ⟨a ∘ p1 A one,p2 A one⟩ = a ∘ p1 A one’ by cheat >>
               rw[] >>
               ‘i1 one one ∘ to1 A o p1 A one = i1 one one ∘ to1 (A × one)’
                 suffices_by cheat >>
               ‘to1 A o p1 A one = to1 (A × one)’ by cheat >>
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
             

                    

Theorem Thm5_lemma_1:
∀A X a x. is_mono a ∧ a∶ A → X ∧ x∶ one → X ∧
          ¬(∃x0. x0∶ one → A ∧ a o x0 = x) ⇒
          ∃phi. phi∶ X → (one + one) ∧
                phi o x = i2 one one ∧
                phi o a = (i1 one one) o (to1 A)
Proof
cheat
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
‘j0 o to1 (exp X (one + one))∶ (exp X (one + one)) → exp A (one + one)’
  by metis_tac[compose_hom] >>
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
  by cheat (*mono_epi_fac*) >>
qexistsl_tac [‘A'’,‘a'’] >> simp[] >>
irule mono_epi_is_iso >>
reverse (strip_tac) (* 2 *)
‘∀x. x∶ one → X ∧ (∃x0. x0∶ one → X ∧ a o x0 = x) ⇒
    ∀t. t∶ one → exp X two ∧
        (∃t0. t0∶ one → L ∧ μ o t0 = t) ⇒
        ev X two o ⟨x,t⟩ = i2 one one’ by cheat >>
‘∀x. x∶ one → X ∧ (∃x0. x0∶ one → X ∧ a' o x0 = x) ⇒
     ∃t. t∶ one → exp X two ∧
        (∃t0. t0∶ one → L ∧ μ o t0 = t) ∧
        ev X two o ⟨x,t⟩ = i1 one one’ by cheat >>
‘∀x. x∶ one → X ⇒ ¬((∃x0. x0∶ one → A ∧ a o x0 = x) ∧
                    (∃x0. x0∶ one → A' ∧ a' o x0 = x))’
  by rpt strip_tac >> 

metis_tac[i1_ne_i2] >>
‘∀Q. q1∶ Q → A + A' ∧ q2∶ Q → A + A' ∧
           ¬(Q ≅ zero) ∧
           (copa a a' o q1 = copa a a' o q2) ⇒
           ¬(∃q1' q2'. q1'∶ Q → A ∧ q2'∶ Q → A' ∧
             i1 A A' o q1' = q1 ∧
             i2 A A' o q2' = q2)’
 by rpt strip_tac >>
    ‘∃q0. q0∶ one → Q’ by metis_tac[ax6] >>
    ‘a o q1' o q0∶ one → X ∧
    (∃x0. x0∶one → A ∧ a ∘ x0 = a o q1' o q0) ∧
     ∃x0. x0∶one → A' ∧ a' ∘ x0 = a o q1' o q0’
      suffices_by metis_tac[] >>
    ‘a ∘ q1' ∘ q0∶one → X’ by metis_tac[compose_hom]>>
    rpt strip_tac (* 3 *)
    >- simp[]
    >- qexists_tac ‘q1' ∘ q0’ >> metis_tac[compose_hom]
    
             

                    

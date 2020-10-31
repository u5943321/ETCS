
Overload product_obj = “λA B. po A B”
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC,450), 
                  pp_elements = [TOK "×"], 
                  term_name = "product_obj", paren_style = OnlyIfNecessary}

(*why the three lines does not work...?*)
                  
(*
Overload parallel_product = “λA B f g. pa ((p1 A B) o f) ((p2 A B) o g)”
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC,450), 
                  pp_elements = [TOK "×'"], 
                  term_name = "product_obj", paren_style = OnlyIfNecessary}

*)


val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, 
                  pp_elements = [TOK "⟨", TM, TOK ",",TM, TOK "⟩"], 
                  term_name = "pa", paren_style = OnlyIfNecessary}

                  


Theorem comm_condition_left:
∀A B n f0 g0. g0∶ one → exp A B ∧ f0∶ N → exp A B ∧ n∶ one → N ∧ f0 o n = g0 ⇒
             ((ev A B) o ⟨p1 A N, f0 o (p2 A N)⟩) o ⟨p1 A one, n o (p2 A one)⟩ =
             ⟨p1 A one,n o (p2 A one)⟩
Proof
cheat
QED



Theorem Thm1_case_1:
∀B g h. g∶ one → B ∧ h∶ po N B → B ⇒
        ∃!f. f∶ N → B ∧ f o z = g ∧ f o s = h o ⟨id N, f⟩
Proof
cheat
QED
                

Theorem comm_condition_triangle:
∀h g B f'. h∶ po N B → B ∧ g∶ one → B ∧  ⇒
           f' o z = ⟨z, g⟩  ⇔ ((p2 N B) o f') o z = g         


Theorem thm_1_A_eq_1:
∀g h B. g∶ one → B ∧ h∶ (po (po one N) B) → B ⇒
          ∃f. f∶ po A N → B ∧
               f o (pa (p1 one one) ((p2 A one) o z)) = g ∧
               h o (pa (id (po A N)) f) = f o (pa (p1 A N) ((p2 A N) o s))                 
Proof



Theorem transpose_comm:
∀g h A B f. g∶ A → B ∧ h∶ (po (po A N) B) → B ∧ f∶ po A N → B ⇒
            (f o (pa (p1 A one) ((p2 A one) o z)) = g ∧
            h o (pa (id (po A N)) f) = f o (pa (p1 A N) ((p2 A N) o s))) ⇔
            (tp f) o z = tp g

Proof


Theorem Thm1_comm_eq_condition:
∀A B f g h. g∶ A → B ∧ h∶ (po (po A N) B) → B ∧ f∶ po A N → B ⇒
       ((f o ⟨p1 A one, z o (p2 A one)⟩ = g o (p1 A one) ∧
        h o ⟨id (po A N), f⟩ = f o ⟨p1 A N, s o (p2 A N)⟩) ⇔
        (tp f o z = tp (g o (p1 A one)) ∧
        tp (h o ⟨
                 ⟨p1 A (po N (exp A B)),
                  (p1 N (exp A B)) o p2 A (po N (exp A B))
                 ⟩,
                 (ev A B) o
                 ⟨p1 A (po N (exp A B)), (p2 N (exp A B)) o p2 A (po N (exp A B))⟩⟩) o
         ⟨id N, tp f⟩ = (tp f) o s))
Proof
rw[] >>
qabbrev_tac ‘g' = tp (g o (p1 A one))’ >>
qabbrev_tac ‘h' = tp (h o
                      ⟨⟨p1 A (po N (exp A B)), (p1 N (exp A B)) o p2 A (po N (exp A B))⟩,
                      (ev A B) o
                      ⟨p1 A (po N (exp A B)), (p2 N (exp A B)) o p2 A (po N (exp A B))⟩⟩)’>>
cheat
QED        
        
Theorem Thm_1:
∀g h A B. g∶ A → B ∧ h∶ (po (po A N) B) → B ⇒
          ∃!f. f∶ po A N → B ∧
               f o ⟨p1 A one, z o (p2 A one)⟩ = g o (p1 A one) ∧
               h o ⟨id (po A N), f⟩ = f o ⟨p1 A N, s o (p2 A N)⟩
Proof
rw[] >>
qabbrev_tac ‘g' = tp (g o (p1 A one))’ >>
qabbrev_tac ‘h' = tp (h o
                      ⟨⟨p1 A (po N (exp A B)), (p1 N (exp A B)) o p2 A (po N (exp A B))⟩,
                      (ev A B) o
                      ⟨p1 A (po N (exp A B)), (p2 N (exp A B)) o p2 A (po N (exp A B))⟩⟩)’>>
‘g'∶ one → exp A B’ by cheat >>                                                            ‘h'∶ po N (exp A B) → exp A B’ by cheat >>
drule_all Thm1_case_1 >> strip_tac >>
fs[Once EXISTS_UNIQUE_ALT] >>
qexists_tac ‘(ev A B) o ⟨p1 A N, f o (p2 A N)⟩’ >>
‘f∶N → exp A B’ by metis_tac[] >>
rename [‘fb∶ N → exp A B’] >>
qabbrev_tac ‘f = ev A B ∘ ⟨p1 A N,fb ∘ p2 A N⟩’ >>
‘f∶A×N → B’ by cheat >>
simp[EQ_IMP_THM] >> strip_tac >> strip_tac (* 2 *)
>- rw[] >>
   ‘ tp f' ∘ z = tp (g ∘ p1 A one) ∧
          tp
            (h ∘
             ⟨⟨p1 A (N×exp A B),p1 N (exp A B) ∘ p2 A (N×exp A B)⟩,ev A B ∘
             ⟨p1 A (N×exp A B),p2 N (exp A B) ∘ p2 A (N×exp A B)⟩⟩) ∘
          ⟨id N,tp f'⟩ =
          tp f' ∘ s’ by metis_tac[Thm1_comm_eq_condition] >>
    ‘tp f' = fb’ by cheat >>
    ‘tp f = fb’ by cheat >>
    (*tp eq implies original eq*) >>
    metis_tac[tp_eq]
>- strip_tac >>
   ‘tp f' ∘ z = tp (g ∘ p1 A one) ∧
          tp
            (h ∘
             ⟨⟨p1 A (N×exp A B),p1 N (exp A B) ∘ p2 A (N×exp A B)⟩,ev A B ∘
             ⟨p1 A (N×exp A B),p2 N (exp A B) ∘ p2 A (N×exp A B)⟩⟩) ∘
          ⟨id N,tp f'⟩ =
          tp f' ∘ s’ suffices_by metis_tac[Thm1_comm_eq_condition] >>
    fs[] >>
    ‘tp f = fb’ by cheat >> metis_tac[]
    
(*outlined*)

theory flash19Rev imports flashPub
begin
section{*Main defintions*}
lemma NI_FAckVsInv19:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_FAck ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvVsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Inv  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1  a2  a3  a4 , auto)
 lemma NI_InvAck_1VsInv19:  
    (*Rule2VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_InvAck_1  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvAck_1_HomeVsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_InvAck_1_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1  a2  a3  a4 , auto)
 lemma NI_InvAck_2VsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_InvAck_2 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1  a2  a3  a4 , auto)
 lemma NI_Local_GetX_GetXVsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_GetX_GetX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Global ''NakcMsg_Cmd'') )  ( Const NAKC_Nakc ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_Nak1VsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_GetX_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_Nak2VsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_GetX_Nak2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_Nak3VsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_GetX_Nak3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX1VsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_GetX_PutX1 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX2VsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_GetX_PutX2 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX3VsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_GetX_PutX3 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX4VsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_GetX_PutX4 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX5VsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_GetX_PutX5 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX6VsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_GetX_PutX6 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX7VsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_GetX_PutX7 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX8VsInv19:  
    (*Rule2VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_GetX_PutX8 N  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX8_homeVsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_GetX_PutX8_home N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX9VsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_GetX_PutX9 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX10VsInv19:  
    (*Rule2VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_GetX_PutX10 N  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX10_homeVsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_GetX_PutX10_home N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX11VsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_GetX_PutX11 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_GetVsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_Get_Get  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Nak1VsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_Get_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Nak2VsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_Get_Nak2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Nak3VsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_Get_Nak3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Put1VsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_Get_Put1 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Put2VsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_Get_Put2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Put3VsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_Get_Put3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_PutVsInv19:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_Put ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_PutXAcksDoneVsInv19:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Local_PutXAcksDone ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_NakVsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Nak  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Nak_ClearVsInv19:  
  (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Nak_Clear ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
  fix s 
 
  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Nak_HomeVsInv19:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Nak_Home ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
 
 

lemma lemmaOnPtrAtGetX[intro]:
  assumes  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 
    and a5:"formEval ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX )) s" and
    a6:"formEval   ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2)) s " and
    a7:"\<forall>f. f \<in> (invariants   N) \<longrightarrow> formEval f s "
 shows  "formEval ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2) )  s"
 proof(rule ccontr)
  assume b0:"\<not>formEval ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2) )  s"
  have b1:"formEval (inv2 iInv1 iInv2) s"
    apply(cut_tac a7)
    
    apply(drule_tac x="inv2  iInv1 iInv2" in spec)
    apply(cut_tac a7 a2 a3 a4,simp)
    done
 with b0 a5 a6 show False
  by auto
qed  



lemma lemmaOnPtrAtGet[intro]:
  assumes  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 
    and a5:"formEval ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get )) s" and
    a6:"formEval   ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2)) s " and
    a7:"\<forall>f. f \<in> (invariants   N) \<longrightarrow> formEval f s "
 shows  "formEval ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2) )  s"
 proof(rule ccontr)
  assume b0:"\<not>formEval ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2) )  s"
  have b1:"formEval (inv3 iInv1 iInv2) s"
    apply(cut_tac a7)
    
    apply(drule_tac x="inv3  iInv1 iInv2" in spec)
    apply(cut_tac a7 a2 a3 a4,simp)
    done
 with b0 a5 a6 show False
  by auto
qed  

lemma lemmaOnPtr1[intro]:
  assumes  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 
    and a5:"formEval ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get )) s" and
    a6:"formEval   ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2)) s " and
    a7:"\<forall>f. f \<in> (invariants   N) \<longrightarrow> formEval f s " and
    b2:"iInv1' \<le> N" and  b3:"iInv2' \<le> N" and  b4:"iInv1'~=iInv2'  " 
    and b5:"formEval ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1') )  ( Const UNI_Get )) s" and
    b6:"formEval   ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1') )   (Const iInv2')) s " and
    b7:"iInv2\<noteq>iInv2'"
 shows False
 proof -
  have c1:"formEval ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2) )  s"
    by(metis a2 a3 a4 a5 a6 a7 lemmaOnPtrAtGet)
  have c2:"formEval ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2') )  s"
    by(metis b2 b3 b4 b5 b6 a7 lemmaOnPtrAtGet)
 with c1 b7  show False
  by auto
qed  


lemma lemmaOnPtr2[intro]:
  assumes  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 
    and a5:"formEval ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX )) s" and
    a6:"formEval   ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2)) s " and
    a7:"\<forall>f. f \<in> (invariants   N) \<longrightarrow> formEval f s " and
    b2:"iInv1' \<le> N" and  b3:"iInv2' \<le> N" and  b4:"iInv1'~=iInv2'  " 
    and b5:"formEval ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1') )  ( Const UNI_GetX )) s" and
    b6:"formEval   ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1') )   (Const iInv2')) s " and
    b7:"iInv2\<noteq>iInv2'"
 shows False
 proof -
  have c1:"formEval ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2) )  s"
    by(metis a2 a3 a4 a5 a6 a7 lemmaOnPtrAtGetX)
  have c2:"formEval ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2') )  s"
    by(metis b2 b3 b4 b5 b6 a7 lemmaOnPtrAtGetX)
 with c1 b7  show False
  by auto
qed 


lemma lemmaOnPtr3[intro]:
  assumes  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 
    and a5:"formEval ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get )) s" and
    a6:"formEval   ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2)) s " and
    a7:"\<forall>f. f \<in> (invariants   N) \<longrightarrow> formEval f s " and
    b2:"iInv1' \<le> N" and  b3:"iInv2' \<le> N" and  b4:"iInv1'~=iInv2'  " 
    and b5:"formEval ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1') )  ( Const UNI_GetX )) s" and
    b6:"formEval   ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1') )   (Const iInv2')) s " and
    b7:"iInv2\<noteq>iInv2'"
 shows False
 proof -
  have c1:"formEval ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2) )  s"
    by(metis a2 a3 a4 a5 a6 a7 lemmaOnPtrAtGet)
  have c2:"formEval ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2') )  s"
    by(metis b2 b3 b4 b5 b6 a7 lemmaOnPtrAtGetX)
 with c1 b7  show False
  by auto
qed      
     
  lemma NI_Remote_GetX_NakVsInv19Aux:  
    (*Rule2VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iRule1~=iRule2  " 

  shows  "invHoldForRule'' s (inv19  iInv1  iInv2 ) (NI_Remote_GetX_Nak  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
   

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

      have "invHoldForRule3'  s (inv19  iInv1  iInv2 ) (NI_Remote_GetX_Nak  iRule1  iRule2 ) (invariants   N)" 
            
     

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv2) )   (Const iInv1))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv2) )  ( Const UNI_GetX ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done
      then have "?P3 s" by(rule weak3)
      
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  
      have "invHoldForRule3'  s (inv19  iInv1  iInv2 ) (NI_Remote_GetX_Nak  iRule1  iRule2 ) (invariants   N)" 

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv2) )   (Const iRule2))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv2) )  ( Const UNI_GetX ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
      then have "?P3 s" by(rule weak3)
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)"

                  
       have "invHoldForRule3'  s (inv19  iInv1  iInv2 ) (NI_Remote_GetX_Nak  iRule1  iRule2 ) (invariants   N)" 

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iRule1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iRule1) )   (Const iInv1))  ) ) " in exI,auto)
 
        
        done

        then have "?P3 s" by(rule weak3) 
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)"

                  
      have "invHoldForRule3'  s (inv19  iInv1  iInv2 ) (NI_Remote_GetX_Nak  iRule1  iRule2 ) (invariants   N)" 

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iRule1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iRule1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

        then have "?P3 s" by(rule weak3) 
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                   have "?P3 s"
                  proof( unfold invHoldForRule3''_def,simp only:Let_def,( rule impI)+,                   rule ccontr)
                    assume c1:"\<forall>f'. f' \<in> invariants N \<longrightarrow> formEval f' s" and c2:"formEval (pre (NI_Remote_GetX_Nak iRule1 iRule2)) s "
                    and c3:"\<not> formEval (substFormByStatement (inv19 iInv1 iInv2) (act (NI_Remote_GetX_Nak iRule1 iRule2))) s"
                   have d1:" formEval (eqn (IVar (Para ''UniMsg_Cmd'' iInv1)) (Const UNI_GetX)) s" by(cut_tac b1 c2 c3, auto)
                   have d2:"formEval (eqn (IVar (Para ''UniMsg_Cmd'' iRule1)) (Const UNI_GetX)) s" by(cut_tac b1 c2 c3, auto)
                   have d3:"formEval (eqn (IVar (Para ''UniMsg_proc'' iInv1)) (Const iInv2)) s"  by(cut_tac b1 c2 c3, auto)
                   have d4:"formEval (eqn (IVar (Para ''UniMsg_proc'' iRule1)) (Const iRule2)) s"  by(cut_tac b1 c2 c3, auto)
                    show False thm lemmaOnPtr2
                    apply(cut_tac a1 a2 a3 a4 a5 a6 b1 c1 c2 c3 d1 d2 d3 d4,blast )
                    done
                   qed

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_GetX_Nak_HomeVsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Remote_GetX_Nak_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_GetX ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_GetX ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_GetX ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
 
     
  lemma NI_Remote_GetX_NakVsInv19 : 
    (*Rule2VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Remote_GetX_Nak  iRule1  iRule2 ) (invariants   N)"
by (metis NI_Remote_GetX_NakVsInv19Aux a2 a3 a4 a5 a6 local.a1 strengthEn)
 
lemma NI_Remote_GetX_PutXVsInv19:  
    (*Rule2VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Remote_GetX_PutX  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_GetX_PutX_HomeVsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Remote_GetX_PutX_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1  a2  a3  a4 , auto)
 lemma NI_Remote_Get_Nak1VsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Remote_Get_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Get ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Get ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Get ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_Get_Nak2VsInv19Aux:  
    (*Rule2VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iRule1~=iRule2  " 

  shows  "invHoldForRule'' s (inv19  iInv1  iInv2 ) (NI_Remote_Get_Nak2  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

      have "invHoldForRule3' s (inv19  iInv1  iInv2 ) (NI_Remote_Get_Nak2  iRule1  iRule2 ) (invariants   N)"            
     

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv2) )   (Const iInv1))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv2) )  ( Const UNI_Get ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       then  have "?P3 s" by( rule weak3)
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  
      have "invHoldForRule3' s (inv19  iInv1  iInv2 ) (NI_Remote_Get_Nak2  iRule1  iRule2 ) (invariants   N)"          

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv2) )   (Const iRule2))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv2) )  ( Const UNI_Get ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       then  have "?P3 s" by( rule weak3)
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)"

                  
      have "invHoldForRule3' s (inv19  iInv1  iInv2 ) (NI_Remote_Get_Nak2  iRule1  iRule2 ) (invariants   N)"          

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_proc'' iRule1) )   (Const iInv1))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iRule1) )  ( Const UNI_Get ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

        then  have "?P3 s" by( rule weak3)
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)"

                  
      have "invHoldForRule3' s (inv19  iInv1  iInv2 ) (NI_Remote_Get_Nak2  iRule1  iRule2 ) (invariants   N)"          

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iRule1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iRule1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

        then  have "?P3 s" by( rule weak3)
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                   have "?P3 s"
                  proof( unfold invHoldForRule3''_def,simp only:Let_def,( rule impI)+,                   rule ccontr)
                    assume c1:"\<forall>f'. f' \<in> invariants N \<longrightarrow> formEval f' s" and c2:"formEval (pre (NI_Remote_Get_Nak2 iRule1 iRule2)) s "
                    and c3:"\<not> formEval (substFormByStatement (inv19 iInv1 iInv2) (act (NI_Remote_Get_Nak2 iRule1 iRule2))) s"
                   have d1:" formEval (eqn (IVar (Para ''UniMsg_Cmd'' iInv1)) (Const UNI_GetX)) s" by(cut_tac b1 c2 c3, auto)
                   have d2:"formEval (eqn (IVar (Para ''UniMsg_Cmd'' iRule1)) (Const UNI_Get)) s" by(cut_tac b1 c2 c3, auto)
                   have d3:"formEval (eqn (IVar (Para ''UniMsg_proc'' iInv1)) (Const iInv2)) s"  by(cut_tac b1 c2 c3, auto)
                   have d4:"formEval (eqn (IVar (Para ''UniMsg_proc'' iRule1)) (Const iRule2)) s"  by(cut_tac b1 c2 c3, auto)
                    show False thm lemmaOnPtr2
                    apply(cut_tac a1 a2 a3 a4 a5 a6 b1 c1 c2 c3 d1 d2 d3 d4,blast )
                    done
                   qed

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
 
 lemma NI_Remote_Get_Nak2VsInv19:  
    (*Rule2VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Remote_Get_Nak2  iRule1  iRule2 ) (invariants   N)"
by (metis NI_Remote_Get_Nak2VsInv19Aux a2 a3 a4 a5 a6 local.a1 strengthEn)
  
lemma NI_Remote_Get_Put1VsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Remote_Get_Put1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1  a2  a3  a4 , auto)
 lemma NI_Remote_Get_Put2VsInv19:  
    (*Rule2VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Remote_Get_Put2  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_PutVsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Remote_Put  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_PutXVsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Remote_PutX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_ReplaceVsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Replace  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1  a2  a3  a4 , auto)
 lemma NI_ReplaceHomeVsInv19:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_ReplaceHome ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ReplaceHomeShrVldVsInv19:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_ReplaceHomeShrVld ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ReplaceShrVldVsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_ReplaceShrVld  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1  a2  a3  a4 , auto)
 lemma NI_ShWbVsInv19:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_ShWb N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_WbVsInv19:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (NI_Wb ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_GetX1VsInv19:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (PI_Local_GetX_GetX1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_GetX2VsInv19:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (PI_Local_GetX_GetX2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_PutX1VsInv19:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (PI_Local_GetX_PutX1 N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_PutX2VsInv19:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (PI_Local_GetX_PutX2 N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_PutX3VsInv19:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (PI_Local_GetX_PutX3 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_PutX4VsInv19:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (PI_Local_GetX_PutX4 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_Get_GetVsInv19:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (PI_Local_Get_Get ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_Get_PutVsInv19:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (PI_Local_Get_Put ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_PutXVsInv19:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (PI_Local_PutX ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_ReplaceVsInv19:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (PI_Local_Replace ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Remote_GetVsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (PI_Remote_Get  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma PI_Remote_GetXVsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (PI_Remote_GetX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma PI_Remote_PutXVsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (PI_Remote_PutX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1  a2  a3  a4 , auto)
 lemma PI_Remote_ReplaceVsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (PI_Remote_Replace  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1  a2  a3  a4 , auto)
 lemma StoreVsInv19:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (Store  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1  a2  a3  a4 , auto)
 lemma StoreHomeVsInv19:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv19  iInv1  iInv2 ) (StoreHome ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  end

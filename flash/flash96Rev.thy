theory flash96Rev imports flashPub
begin
section{*Main defintions*}
lemma NI_FAckVsInv96:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv96 ) (NI_FAck ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma NI_InvVsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Inv  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvAck_1VsInv96:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv96 ) (NI_InvAck_1  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvAck_1_HomeVsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_InvAck_1_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvAck_2VsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_InvAck_2 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_GetXVsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_GetX_GetX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_Nak1VsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_GetX_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_Nak2VsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_GetX_Nak2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_Nak3VsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_GetX_Nak3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX1VsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX1 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX2VsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX2 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX3VsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX3 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX4VsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX4 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX5VsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX5 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX6VsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX6 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX7VsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX7 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX8VsInv96:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX8 N  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX8_homeVsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX8_home N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX9VsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX9 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX10VsInv96:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX10 N  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX10_homeVsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX10_home N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX11VsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX11 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_GetVsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_Get_Get  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Nak1VsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_Get_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Nak2VsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_Get_Nak2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Nak3VsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_Get_Nak3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Put1VsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_Get_Put1 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Put2VsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_Get_Put2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Put3VsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Local_Get_Put3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_PutVsInv96:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv96 ) (NI_Local_Put ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Local_PutXAcksDoneVsInv96:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv96 ) (NI_Local_PutXAcksDone ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_NakVsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Nak  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Nak_ClearVsInv96:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv96 ) (NI_Nak_Clear ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma NI_Nak_HomeVsInv96:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv96 ) (NI_Nak_Home ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Remote_GetX_NakVsInv96:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv96 ) (NI_Remote_GetX_Nak  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_GetX_Nak_HomeVsInv96:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Remote_GetX_Nak_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Remote_GetX_PutXVsInv96:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv96 ) (NI_Remote_GetX_PutX  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_GetX_PutX_HomeVsInv96:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Remote_GetX_PutX_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Remote_Get_Nak1VsInv96:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Remote_Get_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Remote_Get_Nak2VsInv96:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv96 ) (NI_Remote_Get_Nak2  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_Get_Put1VsInv96:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Remote_Get_Put1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P3 s"

         
        apply(   cut_tac  a1 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' iRule1) )  ( Const CACHE_E ))    ( eqn ( IVar ( Global ''WbMsg_Cmd'') )  ( Const WB_Wb ))  ) ) " in exI,auto)
 
        
        done

       
       then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

        by blast

  


 qed
lemma NI_Remote_Get_Put2VsInv96:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv96 ) (NI_Remote_Get_Put2  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_PutVsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Remote_Put  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_PutXVsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Remote_PutX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ReplaceVsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_Replace  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ReplaceHomeVsInv96:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv96 ) (NI_ReplaceHome ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma NI_ReplaceHomeShrVldVsInv96:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv96 ) (NI_ReplaceHomeShrVld ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma NI_ReplaceShrVldVsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (NI_ReplaceShrVld  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ShWbVsInv96:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv96 ) (NI_ShWb N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma NI_WbVsInv96:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv96 ) (NI_Wb ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Local_GetX_GetX1VsInv96:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv96 ) (PI_Local_GetX_GetX1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Local_GetX_GetX2VsInv96:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv96 ) (PI_Local_GetX_GetX2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Local_GetX_PutX1VsInv96:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv96 ) (PI_Local_GetX_PutX1 N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_GetX_PutX2VsInv96:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv96 ) (PI_Local_GetX_PutX2 N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_GetX_PutX3VsInv96:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv96 ) (PI_Local_GetX_PutX3 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_GetX_PutX4VsInv96:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv96 ) (PI_Local_GetX_PutX4 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_Get_GetVsInv96:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv96 ) (PI_Local_Get_Get ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Local_Get_PutVsInv96:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv96 ) (PI_Local_Get_Put ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_PutXVsInv96:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv96 ) (PI_Local_PutX ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_ReplaceVsInv96:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv96 ) (PI_Local_Replace ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Remote_GetVsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (PI_Remote_Get  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Remote_GetXVsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (PI_Remote_GetX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Remote_PutXVsInv96:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (PI_Remote_PutX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P3 s"

         
        apply(   cut_tac  a1 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' iRule1) )  ( Const CACHE_E ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Put ))  ) ) " in exI,auto)
 
        
        done

       
       then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

        by blast

  


 qed
lemma PI_Remote_ReplaceVsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (PI_Remote_Replace  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma StoreVsInv96:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv96 ) (Store  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma StoreHomeVsInv96:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv96 ) (StoreHome ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  end

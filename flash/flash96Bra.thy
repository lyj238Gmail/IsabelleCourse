theory flash96Bra  imports flash96Rev
 
  begin
lemma onInv96:

   assumes  

     b1:"r \<in> rules N" and b2:"invf=inv96 "
   shows  "invHoldForRule' s invf r (invariants   N)" 
   proof - 
have c1:"ex1P N (% iRule1 .  r=NI_Local_GetX_PutX1 N  iRule1 )\<or>ex1P N (% iRule1 .  r=NI_Local_GetX_GetX  iRule1 )\<or>ex1P N (% iRule1 .  r=NI_Replace  iRule1 )\<or>ex0P N (  r=NI_ShWb N )\<or>ex0P N (  r=PI_Local_GetX_GetX2 )\<or>ex0P N (  r=NI_Local_PutXAcksDone )\<or>ex1P N (% iRule1 .  r=NI_Local_GetX_PutX7 N  iRule1 )\<or>ex1P N (% iRule1 .  r=NI_Local_Get_Nak2  iRule1 )\<or>ex0P N (  r=NI_ReplaceHomeShrVld )\<or>ex1P N (% iRule1 .  r=NI_Remote_Put  iRule1 )\<or>ex1P N (% iRule1 .  r=NI_Local_GetX_PutX5 N  iRule1 )\<or>ex0P N (  r=NI_Wb )\<or>ex1P N (% iRule1 .  r=NI_Local_Get_Get  iRule1 )\<or>ex0P N (  r=PI_Local_Replace )\<or>ex1P N (% iRule1 .  r=NI_ReplaceShrVld  iRule1 )\<or>ex2P N (% iRule1  iRule2 .  r=NI_Local_GetX_PutX8 N  iRule1  iRule2 )\<or>ex1P N (% iRule1 .  r=NI_InvAck_2 N  iRule1 )\<or>ex2P N (% iRule1  iRule2 .  r=NI_Remote_Get_Nak2  iRule1  iRule2 )\<or>ex1P N (% iRule1 .  r=PI_Remote_Replace  iRule1 )\<or>ex0P N (  r=NI_Nak_Home )\<or>ex1P N (% iRule1 .  r=NI_Local_Get_Put2  iRule1 )\<or>ex2P N (% iRule1  iRule2 .  r=NI_InvAck_1  iRule1  iRule2 )\<or>ex1P N (% iRule1 .  r=NI_Local_GetX_PutX11 N  iRule1 )\<or>ex1P N (% iRule1 .  r=NI_Local_GetX_PutX6 N  iRule1 )\<or>ex2P N (% iRule1  iRule2 .  r=NI_Remote_Get_Put2  iRule1  iRule2 )\<or>ex0P N (  r=PI_Local_Get_Put )\<or>ex0P N (  r=PI_Local_GetX_PutX1 N )\<or>ex1P N (% iRule1 .  r=NI_InvAck_1_Home  iRule1 )\<or>ex1P N (% iRule1 .  r=NI_Remote_Get_Nak1  iRule1 )\<or>ex1P N (% iRule1 .  r=NI_Local_Get_Nak1  iRule1 )\<or>ex1P N (% iRule1 .  r=NI_Local_GetX_Nak2  iRule1 )\<or>ex1P N (% iRule1 .  r=NI_Local_GetX_PutX10_home N  iRule1 )\<or>ex1P N (% iRule1 .  r=PI_Remote_Get  iRule1 )\<or>ex1P N (% iRule1 .  r=NI_Local_GetX_Nak3  iRule1 )\<or>ex2P N (% iRule1  iRule2 .  r=NI_Local_GetX_PutX10 N  iRule1  iRule2 )\<or>ex1P N (% iRule1 .  r=NI_Local_GetX_PutX2 N  iRule1 )\<or>ex1P N (% iRule1 .  r=NI_Remote_Get_Put1  iRule1 )\<or>ex1P N (% iRule1 .  r=NI_Remote_PutX  iRule1 )\<or>ex1P N (% iRule1 .  r=Store  iRule1 )\<or>ex0P N (  r=NI_FAck )\<or>ex1P N (% iRule1 .  r=NI_Local_GetX_PutX3 N  iRule1 )\<or>ex0P N (  r=PI_Local_GetX_PutX3 )\<or>ex2P N (% iRule1  iRule2 .  r=NI_Remote_GetX_PutX  iRule1  iRule2 )\<or>ex1P N (% iRule1 .  r=NI_Local_GetX_PutX8_home N  iRule1 )\<or>ex1P N (% iRule1 .  r=NI_Local_Get_Put1 N  iRule1 )\<or>ex0P N (  r=PI_Local_GetX_GetX1 )\<or>ex0P N (  r=StoreHome )\<or>ex2P N (% iRule1  iRule2 .  r=NI_Remote_GetX_Nak  iRule1  iRule2 )\<or>ex1P N (% iRule1 .  r=NI_Inv  iRule1 )\<or>ex1P N (% iRule1 .  r=PI_Remote_PutX  iRule1 )\<or>ex0P N (  r=PI_Local_GetX_PutX4 )\<or>ex1P N (% iRule1 .  r=NI_Local_GetX_PutX4 N  iRule1 )\<or>ex1P N (% iRule1 .  r=NI_Nak  iRule1 )\<or>ex0P N (  r=PI_Local_GetX_PutX2 N )\<or>ex0P N (  r=NI_Local_Put )\<or>ex1P N (% iRule1 .  r=NI_Local_GetX_Nak1  iRule1 )\<or>ex0P N (  r=NI_Nak_Clear )\<or>ex0P N (  r=PI_Local_PutX )\<or>ex1P N (% iRule1 .  r=NI_Local_Get_Nak3  iRule1 )\<or>ex1P N (% iRule1 .  r=NI_Remote_GetX_Nak_Home  iRule1 )\<or>ex0P N (  r=PI_Local_Get_Get )\<or>ex1P N (% iRule1 .  r=NI_Local_GetX_PutX9 N  iRule1 )\<or>ex1P N (% iRule1 .  r=PI_Remote_GetX  iRule1 )\<or>ex0P N (  r=NI_ReplaceHome )\<or>ex1P N (% iRule1 .  r=NI_Remote_GetX_PutX_Home  iRule1 )\<or>ex1P N (% iRule1 .  r=NI_Local_Get_Put3  iRule1 )" 

        apply(cut_tac  b1)
        apply auto
        done      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_GetX_PutX1 N  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_GetX_PutX1 N  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX1 N  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_GetX_PutX1VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_GetX_GetX  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_GetX_GetX  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_GetX_GetX  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_GetX_GetXVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Replace  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Replace  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Replace  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_ReplaceVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex0P N (  r= NI_ShWb N )
"
         
         from c1 have c2:" r= NI_ShWb N " 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_ShWb N ) (invariants N) "
            apply(cut_tac    b2 c2 )
            by (metis NI_ShWbVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
	}      moreover
        {assume c1: "ex0P N (  r= PI_Local_GetX_GetX2 )
"
         
         from c1 have c2:" r= PI_Local_GetX_GetX2 " 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv96 ) (PI_Local_GetX_GetX2 ) (invariants N) "
            apply(cut_tac    b2 c2 )
            by (metis PI_Local_GetX_GetX2VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
	}      moreover
        {assume c1: "ex0P N (  r= NI_Local_PutXAcksDone )
"
         
         from c1 have c2:" r= NI_Local_PutXAcksDone " 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_PutXAcksDone ) (invariants N) "
            apply(cut_tac    b2 c2 )
            by (metis NI_Local_PutXAcksDoneVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
	}      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_GetX_PutX7 N  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_GetX_PutX7 N  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX7 N  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_GetX_PutX7VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_Get_Nak2  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_Get_Nak2  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_Get_Nak2  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_Get_Nak2VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex0P N (  r= NI_ReplaceHomeShrVld )
"
         
         from c1 have c2:" r= NI_ReplaceHomeShrVld " 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_ReplaceHomeShrVld ) (invariants N) "
            apply(cut_tac    b2 c2 )
            by (metis NI_ReplaceHomeShrVldVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
	}      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Remote_Put  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Remote_Put  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Remote_Put  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Remote_PutVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_GetX_PutX5 N  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_GetX_PutX5 N  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX5 N  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_GetX_PutX5VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex0P N (  r= NI_Wb )
"
         
         from c1 have c2:" r= NI_Wb " 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Wb ) (invariants N) "
            apply(cut_tac    b2 c2 )
            by (metis NI_WbVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
	}      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_Get_Get  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_Get_Get  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_Get_Get  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_Get_GetVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex0P N (  r= PI_Local_Replace )
"
         
         from c1 have c2:" r= PI_Local_Replace " 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv96 ) (PI_Local_Replace ) (invariants N) "
            apply(cut_tac    b2 c2 )
            by (metis PI_Local_ReplaceVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
	}      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_ReplaceShrVld  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_ReplaceShrVld  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_ReplaceShrVld  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_ReplaceShrVldVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex2P N (% iRule1  iRule2 .  r= NI_Local_GetX_PutX8 N  iRule1  iRule2 )
"
         
         from c1 obtain  iRule1  iRule2  where c2:"  iRule1~=iRule2    \<and>   iRule1 \<le> N \<and>   iRule2 \<le> N \<and>  r= NI_Local_GetX_PutX8 N  iRule1  iRule2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX8 N  iRule1  iRule2 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_GetX_PutX8VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_InvAck_2 N  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_InvAck_2 N  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_InvAck_2 N  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_InvAck_2VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex2P N (% iRule1  iRule2 .  r= NI_Remote_Get_Nak2  iRule1  iRule2 )
"
         
         from c1 obtain  iRule1  iRule2  where c2:"  iRule1~=iRule2    \<and>   iRule1 \<le> N \<and>   iRule2 \<le> N \<and>  r= NI_Remote_Get_Nak2  iRule1  iRule2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Remote_Get_Nak2  iRule1  iRule2 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Remote_Get_Nak2VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= PI_Remote_Replace  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= PI_Remote_Replace  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (PI_Remote_Replace  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis PI_Remote_ReplaceVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex0P N (  r= NI_Nak_Home )
"
         
         from c1 have c2:" r= NI_Nak_Home " 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Nak_Home ) (invariants N) "
            apply(cut_tac    b2 c2 )
            by (metis NI_Nak_HomeVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
	}      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_Get_Put2  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_Get_Put2  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_Get_Put2  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_Get_Put2VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex2P N (% iRule1  iRule2 .  r= NI_InvAck_1  iRule1  iRule2 )
"
         
         from c1 obtain  iRule1  iRule2  where c2:"  iRule1~=iRule2    \<and>   iRule1 \<le> N \<and>   iRule2 \<le> N \<and>  r= NI_InvAck_1  iRule1  iRule2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_InvAck_1  iRule1  iRule2 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_InvAck_1VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_GetX_PutX11 N  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_GetX_PutX11 N  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX11 N  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_GetX_PutX11VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_GetX_PutX6 N  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_GetX_PutX6 N  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX6 N  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_GetX_PutX6VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex2P N (% iRule1  iRule2 .  r= NI_Remote_Get_Put2  iRule1  iRule2 )
"
         
         from c1 obtain  iRule1  iRule2  where c2:"  iRule1~=iRule2    \<and>   iRule1 \<le> N \<and>   iRule2 \<le> N \<and>  r= NI_Remote_Get_Put2  iRule1  iRule2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Remote_Get_Put2  iRule1  iRule2 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Remote_Get_Put2VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex0P N (  r= PI_Local_Get_Put )
"
         
         from c1 have c2:" r= PI_Local_Get_Put " 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv96 ) (PI_Local_Get_Put ) (invariants N) "
            apply(cut_tac    b2 c2 )
            by (metis PI_Local_Get_PutVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
	}      moreover
        {assume c1: "ex0P N (  r= PI_Local_GetX_PutX1 N )
"
         
         from c1 have c2:" r= PI_Local_GetX_PutX1 N " 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv96 ) (PI_Local_GetX_PutX1 N ) (invariants N) "
            apply(cut_tac    b2 c2 )
            by (metis PI_Local_GetX_PutX1VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
	}      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_InvAck_1_Home  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_InvAck_1_Home  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_InvAck_1_Home  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_InvAck_1_HomeVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Remote_Get_Nak1  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Remote_Get_Nak1  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Remote_Get_Nak1  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Remote_Get_Nak1VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_Get_Nak1  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_Get_Nak1  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_Get_Nak1  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_Get_Nak1VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_GetX_Nak2  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_GetX_Nak2  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_GetX_Nak2  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_GetX_Nak2VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_GetX_PutX10_home N  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_GetX_PutX10_home N  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX10_home N  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_GetX_PutX10_homeVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= PI_Remote_Get  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= PI_Remote_Get  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (PI_Remote_Get  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis PI_Remote_GetVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_GetX_Nak3  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_GetX_Nak3  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_GetX_Nak3  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_GetX_Nak3VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex2P N (% iRule1  iRule2 .  r= NI_Local_GetX_PutX10 N  iRule1  iRule2 )
"
         
         from c1 obtain  iRule1  iRule2  where c2:"  iRule1~=iRule2    \<and>   iRule1 \<le> N \<and>   iRule2 \<le> N \<and>  r= NI_Local_GetX_PutX10 N  iRule1  iRule2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX10 N  iRule1  iRule2 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_GetX_PutX10VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_GetX_PutX2 N  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_GetX_PutX2 N  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX2 N  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_GetX_PutX2VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Remote_Get_Put1  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Remote_Get_Put1  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Remote_Get_Put1  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Remote_Get_Put1VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Remote_PutX  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Remote_PutX  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Remote_PutX  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Remote_PutXVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= Store  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= Store  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (Store  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis StoreVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex0P N (  r= NI_FAck )
"
         
         from c1 have c2:" r= NI_FAck " 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_FAck ) (invariants N) "
            apply(cut_tac    b2 c2 )
            by (metis NI_FAckVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
	}      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_GetX_PutX3 N  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_GetX_PutX3 N  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX3 N  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_GetX_PutX3VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex0P N (  r= PI_Local_GetX_PutX3 )
"
         
         from c1 have c2:" r= PI_Local_GetX_PutX3 " 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv96 ) (PI_Local_GetX_PutX3 ) (invariants N) "
            apply(cut_tac    b2 c2 )
            by (metis PI_Local_GetX_PutX3VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
	}      moreover
        {assume c1: "ex2P N (% iRule1  iRule2 .  r= NI_Remote_GetX_PutX  iRule1  iRule2 )
"
         
         from c1 obtain  iRule1  iRule2  where c2:"  iRule1~=iRule2    \<and>   iRule1 \<le> N \<and>   iRule2 \<le> N \<and>  r= NI_Remote_GetX_PutX  iRule1  iRule2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Remote_GetX_PutX  iRule1  iRule2 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Remote_GetX_PutXVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_GetX_PutX8_home N  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_GetX_PutX8_home N  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX8_home N  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_GetX_PutX8_homeVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_Get_Put1 N  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_Get_Put1 N  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_Get_Put1 N  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_Get_Put1VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex0P N (  r= PI_Local_GetX_GetX1 )
"
         
         from c1 have c2:" r= PI_Local_GetX_GetX1 " 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv96 ) (PI_Local_GetX_GetX1 ) (invariants N) "
            apply(cut_tac    b2 c2 )
            by (metis PI_Local_GetX_GetX1VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
	}      moreover
        {assume c1: "ex0P N (  r= StoreHome )
"
         
         from c1 have c2:" r= StoreHome " 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv96 ) (StoreHome ) (invariants N) "
            apply(cut_tac    b2 c2 )
            by (metis StoreHomeVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
	}      moreover
        {assume c1: "ex2P N (% iRule1  iRule2 .  r= NI_Remote_GetX_Nak  iRule1  iRule2 )
"
         
         from c1 obtain  iRule1  iRule2  where c2:"  iRule1~=iRule2    \<and>   iRule1 \<le> N \<and>   iRule2 \<le> N \<and>  r= NI_Remote_GetX_Nak  iRule1  iRule2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Remote_GetX_Nak  iRule1  iRule2 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Remote_GetX_NakVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Inv  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Inv  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Inv  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_InvVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= PI_Remote_PutX  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= PI_Remote_PutX  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (PI_Remote_PutX  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis PI_Remote_PutXVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex0P N (  r= PI_Local_GetX_PutX4 )
"
         
         from c1 have c2:" r= PI_Local_GetX_PutX4 " 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv96 ) (PI_Local_GetX_PutX4 ) (invariants N) "
            apply(cut_tac    b2 c2 )
            by (metis PI_Local_GetX_PutX4VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
	}      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_GetX_PutX4 N  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_GetX_PutX4 N  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX4 N  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_GetX_PutX4VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Nak  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Nak  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Nak  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_NakVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex0P N (  r= PI_Local_GetX_PutX2 N )
"
         
         from c1 have c2:" r= PI_Local_GetX_PutX2 N " 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv96 ) (PI_Local_GetX_PutX2 N ) (invariants N) "
            apply(cut_tac    b2 c2 )
            by (metis PI_Local_GetX_PutX2VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
	}      moreover
        {assume c1: "ex0P N (  r= NI_Local_Put )
"
         
         from c1 have c2:" r= NI_Local_Put " 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_Put ) (invariants N) "
            apply(cut_tac    b2 c2 )
            by (metis NI_Local_PutVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
	}      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_GetX_Nak1  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_GetX_Nak1  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_GetX_Nak1  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_GetX_Nak1VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex0P N (  r= NI_Nak_Clear )
"
         
         from c1 have c2:" r= NI_Nak_Clear " 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Nak_Clear ) (invariants N) "
            apply(cut_tac    b2 c2 )
            by (metis NI_Nak_ClearVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
	}      moreover
        {assume c1: "ex0P N (  r= PI_Local_PutX )
"
         
         from c1 have c2:" r= PI_Local_PutX " 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv96 ) (PI_Local_PutX ) (invariants N) "
            apply(cut_tac    b2 c2 )
            by (metis PI_Local_PutXVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
	}      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_Get_Nak3  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_Get_Nak3  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_Get_Nak3  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_Get_Nak3VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Remote_GetX_Nak_Home  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Remote_GetX_Nak_Home  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Remote_GetX_Nak_Home  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Remote_GetX_Nak_HomeVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex0P N (  r= PI_Local_Get_Get )
"
         
         from c1 have c2:" r= PI_Local_Get_Get " 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv96 ) (PI_Local_Get_Get ) (invariants N) "
            apply(cut_tac    b2 c2 )
            by (metis PI_Local_Get_GetVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
	}      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_GetX_PutX9 N  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_GetX_PutX9 N  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_GetX_PutX9 N  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_GetX_PutX9VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= PI_Remote_GetX  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= PI_Remote_GetX  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (PI_Remote_GetX  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis PI_Remote_GetXVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex0P N (  r= NI_ReplaceHome )
"
         
         from c1 have c2:" r= NI_ReplaceHome " 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_ReplaceHome ) (invariants N) "
            apply(cut_tac    b2 c2 )
            by (metis NI_ReplaceHomeVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
	}      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Remote_GetX_PutX_Home  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Remote_GetX_PutX_Home  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Remote_GetX_PutX_Home  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Remote_GetX_PutX_HomeVsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }      moreover
        {assume c1: "ex1P N (% iRule1 .  r= NI_Local_Get_Put3  iRule1 )
"
         
         from c1 obtain  iRule1  where c2:"  iRule1 \<le> N \<and>  r= NI_Local_Get_Put3  iRule1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv96 ) (NI_Local_Get_Put3  iRule1 ) (invariants N) "
            apply(cut_tac  c2  )
            by (metis NI_Local_Get_Put3VsInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 b2, metis) 
        }ultimately show "invHoldForRule' s invf r (invariants N) "
          by blast 
     qed
end
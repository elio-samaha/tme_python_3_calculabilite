#============================================#
# UE Calculabilite L3                        #
# TME GHC reduites                           #
# Mathieu.Jaume@lip6.fr                      #
#============================================#

from ghc import *

# Symboles productifs
# -------------------
        
def prod0(t,r):
    # t : symboles terminaux
    # r : liste de productions
    res = []
    for elem, prod in r:
        for der in prod:
            vrai = 1
            for i in der:
                if not is_in(eq_atom , i , t) :
                    vrai = 0
            if vrai == 1:
                res = ajout(eq_atom, elem, res)
 
    return res

def next_prod(t,r,eqnt,prev):
    # t : symboles terminaux
    # r : liste de productions
    # eqnt : egalite sur les non terminaux
    # prev : liste de non terminaux de depart
    res = prev.copy()
    for elem, rp in r:
        for der in rp:
            vrai = 1
            for i in der:
                if not is_in(eqnt , i , t) and not is_in(eqnt , i , prev):
                    vrai = 0
            if vrai == 1:
                res = ajout(eq_atom, elem, res)
 
    return res


def prod(t,r,eqnt):
    # t : symboles terminaux
    # r : liste de productions
    # eqnt : egalite sur les non terminaux        
    def _prod_aux(prev):
        return next_prod(t , r , eqnt , prev)
    return fixpoint_from(make_eq_set(eqnt) , _prod_aux , prod0(t,r))

# Elimination des symboles non productifs d'une GHC
# -------------------------------------------------

# elimination de non-terminaux n'appartenant pas a l'ensemble ent (ainsi que
# des productions contenant un symbole n'appartenant pas a ent

def remove_nt(g,ent):
    # g : ghc
    # ent : symboles non terminaux
    nt,t,r,si,eqnt = g
    def is_terminal(x):
        return is_in(eq_atom,x,t)
    def is_in_ent(x):
        return is_in(eqnt,x,ent)
    def is_in_ent_or_terminal(x):
        return is_in_ent(x) or is_terminal(x)
    def all_in_ent_or_terminal(l):
        return forall_such_that(l,is_in_ent_or_terminal)
    new_r = [(s,[l for l in ls if all_in_ent_or_terminal(l)]) \
             for s,ls in r if is_in_ent(s)]
    if is_in_ent(si):
        return (ent,t,new_r,si,eqnt)
    else:
        return (ent,t,new_r,None,eqnt)


def remove_non_prod(g):
    # g : ghc
    (_,g_t,g_r,_,eq_atom) = g
    return remove_nt(g, prod(g_t,g_r,eq_atom))

# Symboles accessibles
# --------------------

def next_reach(nt,r,eqnt,prev):
    # nt : symboles non terminaux
    # r : liste de productions
    # eqnt : egalite sur les non terminaux
    # prev : liste de non terminaux de depart
    
    res = []

    for s in prev :
        for (si,li) in r :
            if eqnt(s,si):
                for k in li :
                    for j in k :
                        if is_in(eqnt,j,nt) :
                            res = ajout(eqnt, j,res)
    return union(eqnt,res,prev)


def reach(nt,r,si,eqnt):
    # nt : symboles non terminaux
    # r : liste de productions
    # si : symbole de depart
    # eqnt : egalite sur les non terminaux
    def _reach_aux(prev):
        return next_reach(nt , r , eqnt , prev)
    return fixpoint_from(make_eq_set(eqnt) , _reach_aux , [si])


# Elimination des symboles non accessibles d'une GHC
# -------------------------------------------------

def remove_non_reach(g):
    # g : ghc
    (g_nt,g_t,g_r,g_s,eq_atom) = g
    return remove_nt(g, reach(g_nt,g_r,g_s,eq_atom))

# Reduction d'une grammaire hors-contexte
# ---------------------------------------

def reduce_grammar(g):
    # g : ghc
    return remove_non_reach(remove_non_prod(g))

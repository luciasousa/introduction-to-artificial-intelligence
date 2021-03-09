#Lúcia Maria Bessa de Sousa 93086
from semantic_network import *
from bayes_net import *
from constraintsearch import *
from itertools import product
from statistics import mode

class MyBN(BayesNet):
    
    def ancestors(self,v):
        mothers = [m for (m,b) in list(self.dependencies[v].items())[0][0]]
        list_ancestors = mothers
        for m in mothers:
            list_ancestors += self.ancestors(m)
        return list(set(list_ancestors))

    def conjunct(self,list_ancestors):
        list_conj = product([True, False], repeat=len(list_ancestors))
        return list(map(lambda c: list(zip(list_ancestors, c)), list_conj))

    def individual_probabilities(self):
        variables = list(self.dependencies)  #variables, lista de todas as variáveis
        prob_indv = {}
        for v in variables:
            conj = self.conjunct(self.ancestors(v))
            prob = 0.0
            for c in conj:
                prob += self.jointProb(c+[(v, True)])
            #para cada variável atribuir o valor da probabilidade
            prob_indv[v] = prob
        return prob_indv

class MySemNet(SemanticNetwork):
    def __init__(self):
        SemanticNetwork.__init__(self)
        self.saveAssocProp=[]           #lista para guardar as propriedades das associações
        self.most_common_prop=None      #a propriedade mais comum irá ser atribuída a esta variável
    
    def translate_ontology(self):
        list_supertypes = []            #lista de todos os supertypes
        super_subtypes = {}             #dicionário {supertype: lista de subtypes}
        l = []

        #adicionar supertypes à lista
        for d in self.declarations:
            if isinstance(d.relation,Subtype):
                list_supertypes.append(d.relation.entity2)
        list_supertypes = list(set(list_supertypes))
        list_supertypes=sorted(list_supertypes)

        #atribuir valores(subtypes) às chaves(supertypes) no dicionário
        for sup in list_supertypes:
            super_subtypes[sup] = []
            for d in self.declarations:
                if sup == d.relation.entity2:
                    if d.relation.entity1 not in super_subtypes[sup]:
                        super_subtypes[sup].append(d.relation.entity1)
        
        #código para transformar items do dicionário em strings do tipo 'Qx Subtype1(x) or Subtype2(x) ... => Supertype(x)
        st3 =None
        for key in super_subtypes:
            if len(super_subtypes[key]) > 1:
                super_subtypes[key] = [x.capitalize() for x in super_subtypes[key]]
                super_subtypes[key] = sorted(super_subtypes[key])
                st1 = '(x) or '.join(super_subtypes[key])
            else:
                st1 = super_subtypes[key][0].capitalize()
            st3=key.capitalize()
            st2 = 'Qx '+st1+'(x) => '+st3+'(x)'
            l.append(st2)
        return l

    def parents(self,entity):
        p = [d.relation.entity2 for d in self.query_local(e1=entity)
                    if not isinstance(d.relation,Association)]
        return p

    def query_inherit(self,entity,assoc):
        l=[]
        localDecle1 = self.query_local(e1=entity)
        localDecle2 = self.query_local(e2=entity)
        parents = self.parents(entity)
        #associações cujo nome é igual ao assoc
        for d in localDecle1:
            if isinstance(d.relation,Association):
                if d.relation.name==assoc:
                    l.append(d)
        #associações cujo nome do inverso é igual ao assoc
        for d in localDecle2:
            if isinstance(d.relation,Association):
                if d.relation.inverse==assoc:
                    l.append(d)        
        if parents!=None:
            for p in parents:
                l += [i for i in self.query_inherit(p,assoc)]
        return list(set(l))

    def query(self,entity,relname):
        localDecl = self.query_local(e1=entity,relname=relname)
        saveSingleEnt=[]        #lista para guardar entidades de associações com cardinalidade 'single'
        saveSingleDecl=[]       #lista para guardar declarações de associações com cardinalidade 'single'
        saveAssocPropDecl =[]   #lista para guardar declarações de propriedades de associação 
        l=[]
        
        #para cardinalidade 'single'
        for d in localDecl:
            if isinstance(d.relation,Association):
                if d.relation.cardinality == 'single':
                    saveSingleEnt.append(d.relation.entity2)    #guarda entidade
                    saveSingleDecl.append(d)                    #guarda declaração

        #se houver mais do que uma entidade, saber qual é a mais comum e retorna-la
        if len(saveSingleEnt)>1:
            res = mode(saveSingleEnt)
            l.append(res)
            return l
        #se houver exatamente 1 declaração com cardinalidade 'single' remove-a das local declarations
        if len(saveSingleEnt)==1:
            localDecl.remove(saveSingleDecl[0])

        #guardar as propriedades das associações das declarações assim como as declarações
        for d in localDecl:
            if isinstance(d.relation,Association):
                self.saveAssocProp+=[d.relation.assoc_properties()]
                saveAssocPropDecl.append(d)

        #se houver mais do que uma assoc_properties guarda a mais comum
        if len(self.saveAssocProp)>2:
            self.most_common_prop = mode(self.saveAssocProp)
        #se houver 1 ou 2 assoc_properties guarda a primeira
        if len(self.saveAssocProp)>0 and len(self.saveAssocProp)<=2:
            self.most_common_prop = self.saveAssocProp[0]

        #verificar se a declaração tem as propriedades da associação mais comum para guardar entidade
        for d in localDecl:
            if isinstance(d.relation,Association):
                if d.relation.assoc_properties() == self.most_common_prop:
                    l.append(d.relation.entity2)

        #caso seja uma relação de Subtype ou Member, guarda as entidades
        for d in localDecl:
            if isinstance(d.relation,Subtype) or isinstance(d.relation,Member):
                l.append(d.relation.entity2)

        #por fim retorna as entidades guardadas para relações de Subtype ou Member
        for d in localDecl:
            if isinstance(d.relation,Subtype) or isinstance(d.relation,Member):
                return l

        #faz chamada recursiva da função para os parents da entity
        pps = self.parents(entity)
        for p in pps:
            l+=[i for i in self.query(p,relname)]
        self.saveAssocProp=[]

        #para cardinalidade 'multiple' guarda todos os valores possíveis na lista
        #e se se verificar que as propriedades de assossiação são diferentes das mais comuns
        #retira esse valor da lista
        for d in localDecl:
            if isinstance(d.relation,Association):
                if d.relation.cardinality == 'multiple':
                    l.append(d.relation.entity2)          
        for d in localDecl:
            if isinstance(d.relation,Association):
                if d.relation.assoc_properties() != self.most_common_prop:
                    if d.relation.entity2 in l:
                        l.remove(d.relation.entity2)

        return list(set(l))

class MyCS(ConstraintSearch):

    def search_all(self,domains=None,xpto=None):

        all_solutions = []      #lista de todas as soluções possíveis
        if domains==None:
            domains = self.domains

        if any([lv==[] for lv in domains.values()]):
            return None

        if all([len(lv)==1 for lv in list(domains.values())]):
            return { v:lv[0] for (v,lv) in domains.items() }
    
        for var in domains.keys():
            if len(domains[var])>1:
                for val in domains[var]:
                    newdomains = dict(domains)
                    newdomains[var] = [val]
                    edges = [(v1,v2) for (v1,v2) in self.constraints if v2==var]
                    newdomains = self.constraint_propagation(newdomains,edges)
                    solution = self.search(newdomains)
                    #se solução diferente de None e não estiver na lista de soluções então adiciona
                    if solution != None and solution not in all_solutions:
                        all_solutions.append(solution)
        return all_solutions
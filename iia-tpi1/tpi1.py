#Lúcia Maria Bessa de Sousa 93086

from tree_search import *
from cidades import *
from strips import *
from more_itertools import unique_everseen
from more_itertools import locate

class MyTree(SearchTree):

    def __init__(self,problem, strategy='breadth', from_init=None, to_goal=None): 
        super().__init__(problem,strategy)
        pi = SearchProblem(self.problem.domain,self.problem.initial,self.problem.domain.middle(self.problem.initial,self.problem.goal))
        pf = SearchProblem(self.problem.domain,self.problem.domain.middle(self.problem.initial,self.problem.goal),self.problem.goal)
        self.from_init = SearchTree(pi,self.strategy)
        self.to_goal = SearchTree(pf,self.strategy)
        self.lista = []
        
    def hybrid1_add_to_open(self,lnewnodes):
        for i in range(len(lnewnodes)): 
            if i%2==0: 
                self.open_nodes.insert(0,lnewnodes[i])
            else:
                self.open_nodes.append(lnewnodes[i]) 
  
    def hybrid2_add_to_open(self,lnewnodes):
        self.open_nodes += lnewnodes
        self.open_nodes.sort(key = lambda node: node.depth - node.offset)
        
    def search2(self):
        while self.open_nodes != []:
            naux = self.open_nodes.pop(0)
            node = MyNode(naux.state,naux.parent)
            if self.problem.goal_test(node.state):
                self.terminal = len(self.open_nodes)+1
                self.solution = node
                return self.get_path(node)
            self.non_terminal+=1
            node.children = []
            for a in self.problem.domain.actions(node.state):
                newstate = self.problem.domain.result(node.state,a)
                if newstate not in self.get_path(node):
                    newnode = MyNode(newstate,node)
                    self.lista.append(newnode)
                    for n in self.lista:
                        if n.depth == newnode.depth:
                            newnode.offset += 1
                    node.children.append(newnode)
            self.add_to_open(node.children)
        return None

    def search_from_middle(self):
        fi_search = self.from_init.search()
        tg_search = self.to_goal.search()
        l = fi_search + tg_search
        return list(unique_everseen(l))

class MyNode(SearchNode):
    def __init__(self,state,parent): 
        super().__init__(state,parent)
        self.offset = 0
        if self.parent != None:
            self.depth = self.parent.depth+1
        else:
            self.depth = 0
        
class MinhasCidades(Cidades):
    def middle(self,city1,city2):
        h = []
        for i in self.coordinates:
            if i != city1 and i != city2:
                h1 = self.heuristic(city1,i)
                h2 = self.heuristic(i,city2)
                h3 = h1 + h2
                h = h + [h3]
        h.sort()
        for j in self.coordinates:
            if i != city1 and i != city2:
                h1 = self.heuristic(city1,j)
                h2 = self.heuristic(j,city2)
                h3 = h1+h2
                if h3 == h[0]:
                    return j

class MySTRIPS(STRIPS):
    def result(self, state, action):
        newstate = [s for s in state if s not in action.neg]
        newstate = newstate + action.pos
        return newstate
        
    def sort(self,state):
        l = []
        for i in range(len(state)):
            l = l + [str(state[i])]
        return sorted(l)




    

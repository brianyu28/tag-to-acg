import copy
import json
import sexpdata
import sys

class TAG:
    def __init__(self, contents):
        self.terminals = contents["terminals"]
        self.nonterminals = contents["nonterminals"]
        self.initials = TAG.parseTrees(contents["initials"])
        self.auxiliaries = TAG.parseTrees(contents["auxiliaries"])
        self.distinguished = contents["distinguished"]
        self.numberTrees()

    def parseTrees(trees):
        return [TAG.parseTree(tree) for tree in trees]

    def parseTree(tree):
        """Parses tree as text as S-expression into nested lists."""
        def parseSymList(symList):
            if isinstance(symList, list):
                return Tree(root=symList[0].value(),
                            children=list(map(parseSymList, symList[1:])))
            else:
                return Tree(root=symList.value(), children=[])
        if not (tree.startswith("(") and tree.endswith(")")):
            tree = "(" + tree + ")"
        data = sexpdata.loads(tree)
        tree = parseSymList(data)
        return tree

    def numberTrees(self):
        """Assigns a unique identifying number to each tree."""
        count = 0
        for tree in self.initials:
            tree.identifier = f"C_TI{count}"
            count += 1
        for tree in self.auxiliaries:
            tree.identifier = f"C_TA{count}"
            count += 1

class Tree:
    def __init__(self, root=None, children=None):
        self.identifier = None # unique identifier to define trees
        self.varname = None  # var name for use for generating lambda expressions
        self.children = children if children is not None else []

        # check for nonadjoining
        if ACG.is_nonterminal(root) and root.endswith("_NA"):
            root = root.rstrip("_NA")
            self.nonadjoining = True
        else:
            self.nonadjoining = False

        # If root ends with a *, it's a foot node
        if root is not None and root.endswith("*"):
            root = root.rstrip("*")
            self.footnode = True
        else:
            self.footnode = False

        self.root = root

    def __str__(self):
        children = ", ".join(list(map(lambda t: t.__str__(), self.children)))
        if children != "":
            children = " (" + children + ")"
        return self.root + children

class ACG:
    def __init__(self, tag):
        self.tag = tag
        self.signatures = []
        self.lexicons = []
        self.metadata = {}  # metadata to store data to be reused
        self.generateACG()

    def generateACG(self):
        self.generateDerivationTrees()
        self.generateDerivedTreeConstants()
        self.generateDerivedTrees()
        self.generateStringSignature()
        self.generateAbsLexicon()
        self.generateYieldLexicons()
        self.generateFullLexicon()
        print("Done generating ACG")

    def generateDerivationTrees(self):
        print("Generating derivation trees...")
        signature = Signature("Derivation_trees")

        # Nonterminal nodes each become two types
        for nonterminal in self.tag.nonterminals:
            signature.addType(f"{nonterminal}_S")
            signature.addType(f"{nonterminal}_A")

        # Definte constants for initial trees 
        for tree in self.tag.initials:
            constant = tree.identifier
            t = ACG.typeForTree(tree, initial=True)
            signature.addConstant(constant, t)

        for tree in self.tag.auxiliaries:
            constant = tree.identifier
            t = ACG.typeForTree(tree, initial=False)
            signature.addConstant(constant, t)

        for nonterminal in self.tag.nonterminals:
            constant = f"I_{nonterminal}"
            signature.addConstant(constant, f"{nonterminal}_A")

        self.signatures.append(signature)

    def typeForTree(tree, initial):
        """Returns the type of an initial tree."""
        interior_nodes = []
        substitution_nodes = []
        
        # Do a DFS of the tree, adding to nodes.
        footnodeIsNonadjoining = False
        def traverse(tree):
            nonlocal footnodeIsNonadjoining
            if ACG.is_nonterminal(tree.root) and not tree.footnode:
                if len(tree.children) > 0:
                    if not tree.nonadjoining:
                        interior_nodes.append(f"{tree.root}_A")
                else:
                    if not tree.nonadjoining:
                        substitution_nodes.append(f"{tree.root}_S")
            for child in tree.children:
                traverse(child)

            # While doing the DFS, check for a nonadjoining footnode. 
            if tree.footnode and tree.nonadjoining:
                footnodeIsNonadjoining = True
        traverse(tree)

        if initial:
            root = [f"{tree.root}_S"]
        elif footnodeIsNonadjoining:
            root = [f"{tree.root}_A"]
        else:
            root = [f"{tree.root}_A -> {tree.root}_A"]

        nodes = interior_nodes + substitution_nodes + root
        return " -> ".join(nodes)

    def generateDerivedTreeConstants(self):
        constants = []
        branching = { nonterminal: 0 for nonterminal in self.tag.nonterminals }

        # Do a DFS of the tree and identify maximal branching
        def traverse(tree):
            if ACG.is_nonterminal(tree.root):
                numChildren = len(tree.children)
                root = tree.root
                if numChildren > branching[root]:
                    branching[root] = numChildren
                for child in tree.children:
                    traverse(child)
        for tree in (self.tag.initials + self.tag.auxiliaries):
            traverse(tree)

        for nonterminal in branching:
            for i in range(1, branching[nonterminal] + 1):
                constants.append({"symbol": f"{nonterminal}_{i}", "size": i})
        
        self.metadata["derivedTreeConstants"] = constants


    def generateDerivedTrees(self):
        print("Generating derived trees...")
        signature = Signature("Derived_trees")
        TREE = ACG.treeTypeOfLength(1)
        signature.addType(TREE)

        # constants of type T for every terminal symbol
        for terminal in self.tag.terminals:
            signature.addConstant(terminal, TREE)

        for constant in self.metadata["derivedTreeConstants"]:
            signature.addConstant(constant["symbol"], ACG.treeTypeOfLength(constant["size"] + 1))
        
        signature.addConstant("Empty", TREE)
        
        self.signatures.append(signature)

    def treeTypeOfLength(x):
        trees = ["tree"] * x
        return " -> ".join(trees)

    def generateStringSignature(self):
        print("Generating string signature...")
        signature = Signature("Strings")
        signature.addType("o")
        signature.addType("string = o->o")
        signature.addConstant("infix + = lambda x y z. x (y z)", "string -> string -> string")
        for terminal in self.tag.terminals:
            signature.addConstant(terminal, "string")
        signature.addConstant("E = lambda lvar. lvar", "string")
        self.signatures.append(signature)

    def generateAbsLexicon(self):
        print("Generating abstract lexicon...")
        lexicon = Lexicon("Abs", "Derivation_trees", "Derived_trees")

        for nonterminal in self.tag.nonterminals:
            lexicon.addMapping(f"{nonterminal}_S", "tree")
            lexicon.addMapping(f"{nonterminal}_A", "tree -> tree")

        for tree in self.tag.initials:
            expr = ACG.lambdaRealizationOfTree(tree, True)
            lexicon.addMapping(tree.identifier, expr)
        for tree in self.tag.auxiliaries:
            expr = ACG.lambdaRealizationOfTree(tree, False)
            lexicon.addMapping(tree.identifier, expr)

        identity = "lambda lvar. lvar"
        for nonterminal in self.tag.nonterminals:
            constant = f"I_{nonterminal}"
            lexicon.addMapping(constant, identity)
        self.lexicons.append(lexicon)

    def lambdaRealizationOfTree(tree, initial):
        """Returns lambda expression encoding a tree."""

        # Use a copy of the tree because we'll mutate it to add vars
        tree = copy.deepcopy(tree)
        print(tree)

        # Get variables
        interiorVars = []
        substitutionVars = []
        footnodeVars = []
        i = 0
        def varTraverse(tree):
            nonlocal i
            tree.varname = f"lvar{i}"
            if ACG.is_nonterminal(tree.root):
                if len(tree.children) > 0:
                    if not tree.nonadjoining:
                        interiorVars.append(tree.varname)
                else:
                    if not tree.nonadjoining:
                        substitutionVars.append(tree.varname)
                i += 1
            for child in tree.children:
                varTraverse(child)
        varTraverse(tree)

        # Auxiliary trees need a special footnode variable 'x'
        if initial == False:
            footnodeVars.append("lvar")

        allVars = interiorVars + substitutionVars + footnodeVars
        lambdaVars = "lambda " + " ".join(allVars) + "."

        def constructExpression(tree):
            # For terminal symbols, just return the symbol
            if not ACG.is_nonterminal(tree.root):
                return tree.root

            # If it's a footnode, use special footnode var 'x'
            if tree.footnode:
                if tree.nonadjoining:
                    return "lvar"
                else:
                    return f"{tree.varname} lvar"

            # For nonterminal symbols, we need an expression
            childExpressions = ["(" + constructExpression(child) + ")" for child in tree.children]
            if tree.nonadjoining:
                return f"({tree.root}_{len(childExpressions)} " + " ".join(childExpressions) + ")"
            else:
                return f"{tree.varname} ({tree.root}_{len(childExpressions)} " + " ".join(childExpressions) + ")"

        expr = constructExpression(tree)
        return f"{lambdaVars} {expr}"

    def generateYieldLexicons(self):
        print("Generating yield lexicon...")
        lexicon = Lexicon("Yield", "Derived_trees", "Strings")
        lexicon.addMapping("tree", "string")
        for terminal in self.tag.terminals:
            lexicon.addMapping(terminal, terminal)

        def concatFunctionOfLength(length):
            variables = []
            for i in range(length):
                variables.append(f"x{i}")
            return "lambda " + " ".join(variables) + ". " + " + ".join(variables)

        for constant in self.metadata["derivedTreeConstants"]:
            lexicon.addMapping(constant["symbol"], concatFunctionOfLength(constant["size"]))
        lexicon.addMapping("Empty", "E")
        self.lexicons.append(lexicon)

    def generateFullLexicon(self):
        print("Generating full lexicon...")
        lexicon = ComposedLexicon("Full", "Abs", "Yield")
        self.lexicons.append(lexicon)

    def is_nonterminal(node):
        return node[0].isupper()

    def output(self, filename):
        f = open(filename, "w")
        for signature in self.signatures:
            signature.output(f)
        for lexicon in self.lexicons:
            lexicon.output(f)
        f.close()

class Signature:
    def __init__(self, name):
        self.name = name
        self.types = []
        self.constants = [] # tuples of (constant, type)

    def addType(self, t):
        self.types.append(t)

    def addConstant(self, constant, t):
        self.constants.append((constant, t))

    def output(self, f):
        self.outputName(f)
        self.outputTypes(f)
        self.outputConstants(f)
        self.outputClosing(f)

    def outputName(self, f):
        f.write(f"signature {self.name} = \n")

    def outputTypes(self, f):
        for t in self.types:
            f.write(f"    {t}: type;\n")
        f.write("\n")

    def outputConstants(self, f):
        for constant, t in self.constants:
            f.write(f"    {constant}: {t};\n")

    def outputClosing(self, f):
        f.write("end\n\n")

class Lexicon():

    def __init__(self, name, first, second):
        self.name = name
        self.first = first
        self.second = second
        self.mappings = []

    def addMapping(self, key, value):
        self.mappings.append((key, value))

    def output(self, f):
        f.write(f"lexicon {self.name}({self.first}): {self.second} = \n")
        for key, value in self.mappings:
            f.write(f"    {key} := {value};\n")
        f.write("end\n\n")

class ComposedLexicon():

    def __init__(self, name, first, second):
        self.name = name
        self.first = first
        self.second = second

    def output(self, f):
        f.write(f"lexicon {self.name} = {self.second} << {self.first}\n\n")

def main():
    inputFilename, outputFilename = parseArguments()
    tag = parseTag(inputFilename)
    acg = generateAcg(tag)
    acg.output(outputFilename)

def parseArguments():
    try:
        return [sys.argv[1], sys.argv[2]]
    except IndexError:
        print("Usage: acgtag input_file.tag output_file.acg", file=sys.stderr)
        sys.exit(1)

def parseTag(inputFilename):
    contents = json.loads(open(inputFilename).read())
    return TAG(contents)

def generateAcg(tag):
    return ACG(tag)

if __name__ == "__main__":
    main()
from tree_sitter import Language, Parser

def travTree(prePos, curNode, id):
  curid = id
  id = id + 1
  rs = [prePos]
  imptType = curNode.type
  types = [imptType]
  imptToken = index2Token(curNode)
  tokens = [imptToken]
  ranges = [None]

  for childNode in curNode.children:
    irs, itypes, itokens, ras, id = travTree(curid, childNode, id)
    rs.extend(irs)
    types.extend(itypes)
    tokens.extend(itokens)
    ranges.extend(ras)

  if (len(curNode.children)!=0):
    ranges[0] = (curid+1, len(tokens))

  return rs, types, tokens, ranges, id

def index2Token(node):
  sLine = node.start_point[0]
  eLine = node.end_point[0]
  s = node.start_point[1]
  e = node.end_point[1]
  if (sLine == eLine):
    sigtoken = codes[sLine][s:e]
  else:
    sigtoken = codes[sLine][s:]
    for i in range(sLine+1, eLine):
      sigtoken = sigtoken + codes[i]
    sigtoken = sigtoken + codes[eLine][:e]
  return sigtoken

def genTree(code, type):
  LANGUAGE = Language('build/my-languages.so', type)
  parser = Parser()
  parser.set_language(LANGUAGE)
  tree = parser.parse(bytes(code, "utf8"))
  return tree

def TreeProc(tree, inputCodes):
  root_node = tree.root_node
  global codes
  codes = inputCodes
  relation, typeList, tokenList, childrenRange, _ = travTree(0, root_node, 0)
  return relation, typeList, tokenList, childrenRange

from ASTparse import TreeProc, genTree
from CodeInput import getCode
from ConfigFile import ConfigFunc, MeteTrainMinGroupNum, VarTrainMinGroupNum, OnlyReadFlag, CallPathDiff, LogEHRRFlag, DetailAnalysis, setGlobalContext
import time, functools
from prefixspan import PrefixSpan
import numpy as np
from prefixspan import PrefixSpan
import copy
import os
import re
import sys
from TemptSave import VarSave, VarLoad, load_and_concatenate, save_variables, save_project, load_variables
from ConfigFile import workingDir, cmdRun
tokenList = []
typeList = []
relation = []
fileTreeList = []
codeList = []
funcDefInfoDict = {}
funcDefSumDict = {}
CallerDict = {}
CallDict = {}
CerList = []
CList = []
skipList = []
treeReachedList = []
nameListForReach = []
funcCallNumDict = {}
branchTypeList = ["if_statement", "while_statement", "switch_statement"]
sys.setrecursionlimit(100000)
hardCodeType = ["string_literal", "number_literal", "char_literal", "null", "false", "true", "__HardCodedVar__"]
defedVarNameList = []
defedVarTypeList = []
GlobalResNameList = []
GlobalResTypeList = []
studyMeteral = []
studyMeteralSource = []
funcCallMark ="**_FUNC_CALL_**"
codeAddMark = "*__ADDED__*"
branchCodeAddMark = "*__Branch__ADDED__*"
basicTypeList = ["int", "char", "double", "float", "bool"]
paternList = []
childRange = []
defedClassName = []
defedClassInfo = []
defedStructName = []
defedStructInfo = []
defedAliasName = []
defedAliasInfo = []
preDefineName = []
preDefineInfo = []
preDefineFuncName = []
preDefineFuncInfo = []
resRepGlobList = []
resRepGlobListFlat = []
rrDataGlobListFlat = []
def FindVarType(name):
    global GlobalResNameList, GlobalResTypeList
    global defedVarNameList, defedVarTypeList
    if (name in defedVarNameList):
        return defedVarTypeList[defedVarNameList.index(name)]
    elif (name in GlobalResNameList):
        return GlobalResTypeList[GlobalResNameList.index(name)]
    else:
        return "__HardCodedVar__"

class ArgInfo:
    def __init__(self, itemList, itemTypeList, bList):
        self.ArgType = "Arg"
        self.itemList = itemList
        self.itemTypeList = itemTypeList
        self.bList = bList
        self.norm = self.NameNormaled()
        self.Item2Str()
    def NameNormaled(self):
        global hardCodeType
        itemNum = len(self.itemList)
        ans = []
        for i in range(itemNum):
            sigItem = self.itemList[i]
            sigType = self.itemTypeList[i]
            if (sigType[0] in hardCodeType):
                if (len(sigItem)!=1):
                    print("NameNormaled Debug Error: This is wired!!!", sigItem)
                ans.append(["__HardCodedVar__"])
            elif (sigType == ["call_expression"]):
                ans.append([sigItem[0].norm])
            else:
                newHead = FindVarType(sigItem[0])
                if (len(sigItem)==1):
                    ans.append([newHead])
                else:
                    imptRepList = [newHead]
                    imptRepList.extend(sigItem[1:])
                    ans.append(imptRepList)
        return ans
    def Item2Str(self):
        ans = []
        for sigItem in self.itemList:
            for ss in sigItem:
                if (isinstance(ss, FuncCallInfo)):
                    ans.append(ss.name)
                elif (isinstance(ss, str)):
                    ans.append(ss)
                else:
                    print("ArgItem2String Error", ss)
                    ans.append(ss)
        self.itemStr = " ".join(ans)
class FuncCallInfo:
    def __init__(self, name, rType, argList, returnList, addressList):
        self.ArgType = "FuncCall"
        self.name = name
        self.rType = rType
        self.argList = argList
        self.returnList = returnList
        self.addressList = addressList
        self.norm = [[funcCallMark+self.name]]
        self.bList = []
        self.isErrorLog = False
        if (argList == None):
            self.bList.append(name)
        else:
            for sigArg in argList:
                if (sigArg != None):
                    self.bList.extend(sigArg.bList)
def ArgItem2String(argA):
    if (argA.ArgType == "FuncCall"):
        return argA.name
    else:
        return argA.itemStr
def ArgInfoCMP(argA, argB):
    if (ArgItem2String(argA)<ArgItem2String(argB)):
        return True
    return False
def consCMP(constrainA, constrainB):
    if (showConstrain(constrainA)<showConstrain(constrainB)):
        return True
    return False
def FuncInfoCMP(FuncA, FuncB):
    if (FuncA.name<FuncB.name):
        return True
    return False
def ItemNeedSwap(itemA, itemB):
    flagArgA = isinstance(itemA, ArgInfo)
    flagArgB = isinstance(itemB, ArgInfo)
    flagFuncA = isinstance(itemB, FuncCallInfo)
    flagFuncB = isinstance(itemB, FuncCallInfo)
    if (flagArgA and flagArgB):
        if (ArgInfoCMP(itemA, itemB) < 0):
            return True
        return False
    elif (flagArgA or flagArgB):
        if (flagArgA):
            return True
        return False
    elif (flagFuncA and flagFuncB):
        if (FuncInfoCMP(itemA, itemB)<0):
            return True
        return False
    elif (flagFuncA or flagFuncB):
        if (flagFuncA):
            return True
        return False
    else:
        if (consCMP(itemA, itemB) < 0):
            return True
        return False

class ConstrantRelation:

    def __init__(self, consList, unconsList, upRRList, upDataList, downRRList, downDataList):
        self.ArgType = "ConstrantRelation"
        self.consList = consList
        self.unconsList = unconsList
        self.ShowConstrainUpdata()
        self.Constrain2Index()
        self.upRRList = upRRList
        self.upDataList = upDataList
        self.downRRList = downRRList
        self.downDataList = downDataList
        self.GenIndexList()
        self.indexList = AssignRemove(self.indexList)
    def ShowConstrainUpdata(self):
        self.showConstrain = showConstrain(self.consList)
    def Constrain2Index(self):
        if (self.showConstrain not in globalContext):
            self.constrainIndex = len(globalContext)
            globalContext.append(self.showConstrain)
        else:
            self.constrainIndex = globalContext.index(self.showConstrain)
    def NewUpAdd(self, newUpindexList):
        global AssignDict
        AssignDict = {}
        IndexListAssignDict(newUpindexList)
        self.upDataList = copy.deepcopy(newUpindexList) + self.upDataList[1:]
        self.consList, _ = ConstrantNormalize(copy.deepcopy(self.unconsList))
        self.ShowConstrainUpdata()
        self.Constrain2Index()
        self.GenIndexList()
        self.indexList = AssignRemove(self.indexList)
    def GenIndexList(self):
        self.indexList = self.upDataList.copy()
        self.indexList.append(self.constrainIndex)
        self.indexList.extend(self.downDataList)
    def normedConstrain(self):
        ans = []
        for sigItem in self.consList:
            if (isinstance(sigItem, list)):
                ans.append(showConstrain(sigItem))
            elif (isinstance(sigItem, str)):
                ans.append(sigItem)
            elif (sigItem.ArgType == "FuncCall"):
                ans.append(sigItem.name)
            else:
                ans.append(MulList2str(sigItem.norm))
        return " ".join(ans)
    def Show(self):
        print("consList", len(self.consList), self.showConstrain)
        print("forwardList")
        fb = len(self.upRRList)
        for i in range(fb):
            print("sigFor", self.upRRList[i])
        print("backwardList", len(self.downRRList))
        lb = len(self.downRRList)
        for i in range(lb):
            print("sigB", i, self.downRRList[i])
def IndexListAssignDict(indexList):
    global AssignDict
    dNum = len(indexList)
    AssignDict = {}
    for i in range(dNum):
        currr = globalContext[indexList[i]]
        if (len(currr) > 6 and currr[:6] == "Assign"):
            curRRList = currr.split()
            if ("=" in curRRList):
                spPos = curRRList.index("=")
                leftVar = " ".join(curRRList[:spPos])
                rightVar = " ".join(curRRList[spPos + 1:])
                if (IsFuncCall(leftVar) == False and IsFuncCall(rightVar) == True):
                    if (leftVar in AssignDict):
                        del AssignDict[leftVar]
                    AssignDict[leftVar] = rightVar

def IsFuncCall(norm):
    global funcCallMark
    fmarkLen = len(funcCallMark)
    if (len(norm)>fmarkLen and norm[:fmarkLen] == funcCallMark):
        return True
    return False
def AssignRemove(indexList):
    global globalContext
    nIndexList = []
    for i in indexList:
        if (i!=None):
            strindex = globalContext[i]
            if (len(strindex)>6 and strindex[:6] == "Assign"):
                continue
        nIndexList.append(i)
    return nIndexList
def ConsListOrderNomalize(consList):
    if (len(consList) != 3):
        print("Wrong format, cons", consList)
        return None
    if (consList[1] == ">=" or consList[1] == ">"):
        temp = consList[0]
        consList[0] = consList[2]
        consList[2] = temp
        if (consList[1] == ">="):
            consList[1] = "<="
        elif (consList[1] == ">"):
            consList[1] = "<"
    elif (consList[1]!="<" and consList[1]!="<="):
        if (ItemNeedSwap(consList[0], consList[2])):
            temp = consList[0]
            consList[0] = consList[2]
            consList[2] = temp
    return consList
def varList2Token(varList):
    ans = []
    nVarList = []
    for i in varList:
        if (tokenList[i] not in ans):
            ans.append(tokenList[i])
            nVarList.append(i)
    return ans, nVarList
def RangeEndPosFind(nodePos):
    global relation, relationLen
    if (nodePos>=relationLen):
        return None
    faterPos = relation[nodePos]
    ans = relationLen-1
    for i in range(nodePos+1, relationLen):
        if relation[i] <= faterPos:
            ans = i - 1
            break
    return ans
def FuncDivide(funcList):
    global funcDefNameList
    custFunc = []
    libFunc = []
    for i in funcList:
        if i in funcDefNameList:
            custFunc.append(i)
        else:
            libFunc.append(i)
    return custFunc, libFunc
def FuncSumApply(nodePos, blanks):
    global funcDefSumDict, tokenList
    funcNamePos = None
    funcCallEndPos = None
    if (typeList[nodePos + 1] == "field_expression"):
        cls = ChildrenList(nodePos)
        funcNamePos, funcCallEndPos = TypeFindInSubTree(nodePos, "field_identifier")
        funcNamePos = funcNamePos[-1]
    else:
        funcNamePos, funcCallEndPos = TypeFindFirstInSubTree(nodePos, "identifier")
    funcName = "*_ERRORFUNC_*"
    argList = []
    addCodeRep = []
    addCodes = []
    if (funcNamePos != None):
        funcName = tokenList[funcNamePos]
        argPos, _ = TypeFindFirstInSubTree(nodePos, "argument_list")
        argList, addCodeRep, addCodes = FuncArgListAnalysis(argPos, blanks)
        addCodeAddMark(addCodes)
    argNum = len(argList)
    if (funcName in funcDefSumDict):
        funcType, argInfo, addrList, argPosList, returnList, returnRelatedRepList, returnDataList, capturedRelation, _, _, _, _, _ = funcDefSumDict[funcName]
        if(len(argInfo)==argNum):
            funcCall = FuncCallInfo(funcName, funcType, argList, returnList, addrList)
        else:
            print("Warning: The argNum doesn't match, skip:", tokenList[nodePos])
            funcCall = FuncCallInfo(funcName, funcType, None, None, None)
    else:
        tempAdList = [1 for _ in argList]
        funcCall = FuncCallInfo(funcName, None, argList, None, tempAdList)
    ErrorLogFlag = False
    if (ErrorLogMatch(nodePos)):
        ErrorLogFlag = True
        funcCall.isErrorLog = True
        addCodeRep.append(["call_expression", True, funcCall])
    else:
        addCodeRep.append(["call_expression", False, funcCall])
    addCodes.append(tokenList[nodePos])
    return funcCall, addCodeRep, addCodes, funcCallEndPos, ErrorLogFlag
def AssignAnalysis(nodePos, blanks, recordFlag = False, createdVarType = None):

    eqPos, assignEndPos = TypeFindInSubTree(nodePos, "=")
    if (eqPos == None):
        print("Error: This assignment have no =!")
        return None
    argList, addCodeRep, addCodes = ArgListAnalysis(nodePos, assignEndPos, blanks)
    leftVar = argList[0]
    if(typeList[nodePos+1] == "identifier" or typeList[nodePos+1] == "pointer_declarator"):
        addCodeRep = addCodeRep[1:]
        addCodes = addCodes[1:]
        addCodeAddMark(addCodes)
    if (recordFlag):
        if (leftVar.itemList[0][0] not in defedVarNameList):
            defedVarNameList.append(leftVar.itemList[0][0])
            defedVarTypeList.append(createdVarType)
    rightVarList = []
    if (len(argList) > 1):
        rightVarList = argList[1:]
    return leftVar, rightVarList, addCodeRep, addCodes, assignEndPos
def PosList2NameList(posList):
    ans = []
    for i in posList:
        ans.append(tokenList[i])
    return ans
def ParaAnalysis(nodePos):
    ans = []
    argList, decEndPos = TypeFindInSubTree(nodePos, "parameter_declaration")
    if (len(argList)==0):
        return ans, decEndPos, []
    argNum = len(argList)
    addressList = []
    for i in range(argNum):
        addressList.append(0)
        sigArg = argList[i]
        cL = ChildrenList(sigArg)
        errorPos, _ = TypeFindFirstInSubTree(sigArg, "ERROR")
        if (errorPos!=None):
            print("This parameteRList have ERROR:", tokenList[nodePos])
            return None, decEndPos, None
        else:
            matchList, _ = TypesFindInSubTree(sigArg, ["pointer_declarator", "array_declarator"])
            if (matchList!=[]):
                addressList[-1] = 1
            argNamePos, rPos = TypeFindFirstInSubTree(sigArg, "identifier")
            if (argNamePos == None):
                continue
            argName = tokenList[argNamePos]
            argTypePos, _ = TypesFindFirstInSubTree(sigArg, ["primitive_type", "type_identifier", "sized_type_specifier"])
            argT = tokenList[argTypePos]
            ans.append([argT, argName])
            defedVarNameList.append(argName)
            defedVarTypeList.append(argT)
    return ans, decEndPos, addressList
def GlobalDeclarProcess(nodePos):
    global GlobalResNameList, GlobalResTypeList
    createdVar, declarEndPos = TypeFindFirstInSubTree(nodePos, "identifier")
    if (createdVar == None):
        print("Warnning: cann't find declarName:", tokenList[nodePos])
    createdVarType, _ = TypesFindFirstInSubTree(nodePos, ["primitive_type", "type_identifier", "sized_type_specifier"])
    if (createdVarType == None):
        print("Warnning: give this up: ", tokenList[nodePos])
        return None, None, declarEndPos
    createdVar = tokenList[createdVar]
    createdVarType = tokenList[createdVarType]
    if(createdVar not in GlobalResNameList):
        GlobalResNameList.append(createdVar)
        GlobalResTypeList.append(createdVarType)
    else:
        print("Warnning: Repeat Var")
        GlobalResTypeList[GlobalResNameList.index(createdVar)] = createdVarType
    return createdVar, createdVarType, declarEndPos
def DeclarProcess(nodePos, blanks):
    createdVarList = []
    leftVarList = []
    rightVarListList = []
    addCodeRep = []
    addCodes = []
    initFlag = False
    createdVarType, declarEndPos = TypesFindFirstInSubTree(nodePos, ["primitive_type", "type_identifier", "sized_type_specifier"])
    if (createdVarType == None):
        return declarEndPos
    createdVarType = tokenList[createdVarType]
    i = nodePos + 1
    while(i<=declarEndPos):
        if (typeList[i] == "identifier"):
            if (tokenList[i] not in defedVarNameList):
                defedVarNameList.append(tokenList[i])
                defedVarTypeList.append(createdVarType)
            imptArg = ArgInfo([[tokenList[i]]], [["Var"]], [[tokenList[i]]])
            createdVarList.append(imptArg)
            i = i + 1
        elif (typeList[i] == "init_declarator"):

            leftVar, rightVarList, aCRep, aCodes, minDecEndPos = AssignAnalysis(i, blanks, True, createdVarType)
            leftVar.norm = [[createdVarType]]
            addCodeAddMark(aCodes)
            addCodeRep.extend(aCRep)
            addCodes.extend(aCodes)
            leftVarList.append(leftVar)
            rightVarListList.append(rightVarList)
            createdVarList.append(leftVar)
            initFlag = True
            i = minDecEndPos + 1
        else:
            i = i + 1
    return initFlag, createdVarList, createdVarType, leftVarList, rightVarListList, addCodeRep, addCodes, declarEndPos
def addCodeAddMark(aCodes):
    global codeAddMark
    an = len(aCodes)
    for i in range(an):
        aCodes[i] = codeAddMark+aCodes[i]
def assertCodeRep(nodePos):
    cLs = ChildrenList(nodePos)
    guardPos, _ = TypeFindFirstInSubTree(nodePos, "argument_list")
    if (guardPos == None):
        print("assertCodeRep Error: Not found parenthesized_expression", tokenList[nodePos])
    temptAns = BranchArgListAnalysis(guardPos)
    constrantList = []
    bList = []
    addCodeRep = []
    addCodes = []
    if (temptAns != None):
        constrantList, bList, cFlag, addCodeRep, addCodes = temptAns
        if (cFlag == False):
            constrantList = [[constrantList, "!=", zeroArg]]
            bList = [bList]
        elif (cFlag == None):
            changeCons = []
            for sigc in constrantList:
                changeCons.append([sigc, "!=", zeroArg])
            constrantList = changeCons
        if (isinstance(constrantList, ArgInfo)):
            print("Error: Debug Here is what we looking fort", constrantList, cFlag)
    return constrantList, bList, addCodeRep, addCodes
def ifCodeRep(nodePos, blanks, codesNum):
    blanks = blanks + "\t"
    ePos = RangeEndPosFind(nodePos)
    guardPos, _ = TypeFindFirstInSubTree(nodePos, "parenthesized_expression")
    if (guardPos == None):
        print("Error: Not found parenthesized_expression", tokenList[nodePos])
    guardEndPos = RangeEndPosFind(guardPos)
    branchVarList, _, _ = ArgListAnalysis(guardPos, guardEndPos, blanks, False)
    temptAns = BranchArgListAnalysis(guardPos)
    constrantList = []
    bList = []
    addCodeRep = []
    addCodes = []
    if (temptAns != None):
        constrantList, bList, cFlag, addCodeRep, addCodes = temptAns
        addCodeAddMark(addCodes)
        if (cFlag == False):
            constrantList = [[constrantList, "!=", zeroArg]]
            bList = [bList]
        elif (cFlag == None):
            changeCons = []
            for sigc in constrantList:
                changeCons.append([sigc, "!=", zeroArg])
            constrantList = changeCons
        if (isinstance(constrantList, ArgInfo)):
            print("Error: Debug Here is what we looking fort", constrantList, cFlag)
    directNodeList = DirectChildrenList(nodePos)
    elsePos = None
    for sigDNode in directNodeList:
        if (typeList[sigDNode] == "else"):
            elsePos = sigDNode
    if (elsePos != None):
        ifCodes, ifCodeRepList, ifCELog,_ = CodeBlockAnalysis(guardEndPos + 1, elsePos-1, blanks, codesNum+len(addCodes)+1)
        elseCodes, elseCodeRepList, elseLog,_ = CodeBlockAnalysis(elsePos + 1, ePos, blanks, codesNum + len(addCodes) + len(ifCodes) +2)
        return True, branchVarList, constrantList, bList, guardPos, ifCodes, ifCodeRepList, elseCodes, elseCodeRepList, ePos, addCodeRep, addCodes
    else:
        ifCodes, ifCodeRepList, ContainErrorLog,_ = CodeBlockAnalysis(guardEndPos + 1, ePos, blanks, codesNum+len(addCodes)+1)

        return False, branchVarList, constrantList, bList, guardPos, ifCodes, ifCodeRepList, None, [], ePos, addCodeRep, addCodes
def switchCodeRep(nodePos, blanks, codesNum):
    blanks = blanks + "\t"
    ePos = RangeEndPosFind(nodePos)
    guardPos, _ = TypeFindFirstInSubTree(nodePos, "parenthesized_expression")
    if (guardPos == None):
        print("Error: Not found parenthesized_expression: ", tokenList[nodePos])
    temptAns = BranchArgListAnalysis(guardPos)
    constrantList = []
    bList = []
    addCodeRep = []
    addCodes = []
    if (temptAns != None):
        constrantList, bList, cFlag, addCodeRep, addCodes = temptAns
        addCodeAddMark(addCodes)
        if (cFlag == False):
            constrantList = [[constrantList, "!=", zeroArg]]
            bList = [bList]
        elif (cFlag == None):
            ansNum = len(constrantList)
            for i in range(ansNum):
                constrantList[i] = [constrantList[i], "!=", zeroArg]
    guardEndPos = RangeEndPosFind(guardPos)
    branchVarList, _, _ = ArgListAnalysis(guardPos, guardEndPos, blanks)
    switchCodes, switchCodeRepList, ContainErrorLog, _ = CodeBlockAnalysis(guardEndPos + 1, ePos, blanks, codesNum +len(addCodes) +1)

    return branchVarList, constrantList, bList, guardPos, switchCodes, switchCodeRepList, ePos, addCodeRep, addCodes
def whileCodeRep(nodePos, blanks, codesNum):
    blanks = blanks + "\t"
    ePos = RangeEndPosFind(nodePos)
    guardPos, _ = TypeFindFirstInSubTree(nodePos, "parenthesized_expression")
    if (guardPos == None):
        print("Error: Not found parenthesized_expression: ", tokenList[nodePos])
    temptAns = BranchArgListAnalysis(guardPos)
    constrantList = []
    bList = []
    addCodeRep = []
    addCodes = []
    if (temptAns != None):
        constrantList, bList, cFlag, addCodeRep, addCodes = temptAns
        addCodeAddMark(addCodes)
        if (cFlag == False):
            constrantList = [[constrantList, "!=", zeroArg]]
            bList = [bList]
        elif (cFlag == None):
            ansNum = len(constrantList)
            for i in range(ansNum):
                constrantList[i] = [constrantList[i], "!=", zeroArg]
    guardEndPos = RangeEndPosFind(guardPos)
    branchVarList, _, _ = ArgListAnalysis(guardPos, guardEndPos, blanks)
    whileCodes, whileCodeRepList, ContainErrorLog,_ = CodeBlockAnalysis(guardEndPos + 1, ePos, blanks, codesNum +len(addCodes)+1)
    return branchVarList, constrantList, bList, guardPos, whileCodes, whileCodeRepList, ePos, addCodeRep, addCodes
def returnCodeRep(nodePos, blanks):
    endPos = RangeEndPosFind(nodePos)
    returnedList, addCodeRep, addCodes = ArgListAnalysis(nodePos + 2, endPos, blanks, False)
    addCodeAddMark(addCodes)
    return returnedList, addCodeRep, addCodes, endPos
guardSigList = [[">", ">=", "<", "<=", "==", "!="], ["&", "|", "+", "-", "*", "\\"], ["!"], ["&&", "||"]]
def InGuardSigList(targetSig):
    global guardSigList
    lenGuardSig = len(guardSigList)
    for i in range(lenGuardSig):
        sigGuardSig = guardSigList[i]
        if targetSig in sigGuardSig:
            return i
    return -1
def ComplexVarAnalysis(pos):
    global guardSigList
    compVarNameList = []
    compVarTypeList = []
    subGroupName = []
    codeRep = []
    cutCodes = []

    uselessList = ["*", "-", ">", ">=", "<", "<=", "==", "!=", "&&", "||", "&", "|", "+", "/", "<<", "!", "%", "comment"]
    if (typeList[pos] == "subscript_expression"):
        directCList = DirectChildrenList(pos)
        targetNamePos = directCList[0]
        pPos = directCList[2]
        leftCNList, leftCTList, leftsGName, leftcRep, leftcCodes = ComplexVarAnalysis(targetNamePos)
        rightCNList, rightCTList, rightsGName, rightcRep, rightcCodes = ComplexVarAnalysis(pPos)
        leftArgInfo = ArgInfo(leftCNList, leftCTList, leftsGName)
        rightArgInfo = ArgInfo(rightCNList, rightCTList, rightsGName)
        compVarNameList = leftCNList
        compVarTypeList = leftCTList
        subGroupName = leftsGName
        cutCodes.extend(leftcCodes)
        codeRep.extend(leftcRep)
        cutCodes.extend(rightcCodes)
        codeRep.extend(rightcRep)
        cutCodes.append(codeAddMark + tokenList[pos])
        codeRep.append(["Subscript", leftArgInfo, rightArgInfo])
    elif (typeList[pos] == "field_expression"):
        directCList = DirectChildrenList(pos)
        targetNamePos = directCList[0]
        pPos = directCList[2]
        leftCNList, leftCTList, leftsGName, leftcRep, leftcCodes = ComplexVarAnalysis(targetNamePos)
        rightCNList, rightCTList, rightsGName, rightcRep, rightcCodes = ComplexVarAnalysis(pPos)
        if (len(leftCNList)!=1):
            print("DebugError: field_expression", tokenList[targetNamePos], typeList[targetNamePos])
        imptList = [tokenList[pos]]
        if (len(leftCNList)>=1):
            imptList = leftCNList[0]
        if (len(rightCNList)>=1):
            imptList.extend(rightCNList[0])
        imptTypeList = ["ErrorField"]
        if (len(leftCTList)>=1):
            imptTypeList = leftCTList[0]
        if (len(rightCTList)>=1):
            imptTypeList.extend(rightCTList[0])
        compVarNameList = [imptList]
        compVarTypeList = [imptTypeList]
        if (len(leftsGName)!=1 or len(rightsGName)!=1):
            print("Wired Field!!!!", len(leftsGName), len(rightsGName))
        subGroupName = [tokenList[pos]]
        if (len(leftsGName)>=1):
            subGroupName = leftsGName[0]
        if (len(rightsGName)>=1):
            subGroupName.extend(rightsGName[0])
        subGroupName= [subGroupName]
        cutCodes.extend(leftcCodes)
        codeRep.extend(leftcRep)
        cutCodes.extend(rightcCodes)
        codeRep.extend(rightcRep)
    elif (typeList[pos] == "identifier" or typeList[pos] == "field_identifier"):
        compVarNameList = [[tokenList[pos]]]
        compVarTypeList = [["Var"]]
        subGroupName = [[tokenList[pos]]]
    elif (typeList[pos] == "pointer_expression"):
        compVarNameList, compVarTypeList, subGroupName, codeRep, cutCodes = ComplexVarAnalysis(pos + 2)
    elif (typeList[pos] == "number_literal" or typeList[pos] == "string_literal" or typeList[pos] in hardCodeType):
        compVarNameList = [[tokenList[pos]]]
        compVarTypeList = [["__HardCodedVar__"]]
        subGroupName = []
    elif (typeList[pos] == "parenthesized_expression"):
        compVarNameList, compVarTypeList, subGroupName, codeRep, cutCodes = ComplexVarAnalysis(pos+2)
    elif (typeList[pos] == "call_expression"):
        funcCall, aCRep, aCodes, fEndPos, _ = FuncSumApply(pos, "")
        aCodes[-1] = codeAddMark + aCodes[-1]
        cutCodes.extend(aCodes)
        codeRep.extend(aCRep)
        compVarNameList = [[funcCall]]
        compVarTypeList = [["call_expression"]]
        if (funcCall.argList!=None):
            subGroupName = [[tokenList[pos]]]
        else:
            subGroupName = []
    elif (typeList[pos] == "sizeof_expression"):
        cLdebugList = ChildrenList(pos)
        aPos, _ = TypeFindFirstInSubTree(pos, "parenthesized_expression")
        if (aPos !=None):
            ePos = RangeEndPosFind(aPos)
            argList, cRep, cCodes = ArgListAnalysis(aPos, ePos, "")

            funcCall = FuncCallInfo("sizeof", None, argList, None, None)
            cutCodes.extend(cCodes)
            codeRep.extend(cRep)
            compVarNameList = [[funcCall]]
            compVarTypeList = [["call_expression"]]
            if (funcCall.argList!=None):

                subGroupName = argList[0].bList
            else:
                subGroupName = []
        else:
            aPos, _ = TypeFindFirstInSubTree(pos, "type_descriptor")
            if (aPos == None):
                ePos = RangeEndPosFind(pos + 1)
                argList, cRep, cCodes = ArgListAnalysis(pos + 1, ePos, "")
                funcCall = FuncCallInfo("sizeof", None, argList, None, None)
                cutCodes.extend(cCodes)
                codeRep.extend(cRep)
                compVarNameList = [[funcCall]]
                compVarTypeList = [["call_expression"]]
                if (funcCall.argList != None and funcCall.argList !=[]):
                    subGroupName = argList[0].bList
                else:
                    subGroupName = []
            else:
                argList = [ArgInfo([[tokenList[aPos]]], [[typeList[aPos]]], [[tokenList[aPos]]])]
                funcCall = FuncCallInfo("sizeof", None, argList, None, None)
                compVarNameList = [[funcCall]]
                compVarTypeList = [["call_expression"]]
                subGroupName = [[tokenList[aPos]]]
    elif (typeList[pos] == "binary_expression" or typeList[pos] == "unary_expression"):
        directCList = DirectChildrenList(pos)
        for sigDir in directCList:
            cNList, cTList, sGName, cRep, cCodes = ComplexVarAnalysis(sigDir)
            compVarNameList.extend(cNList)
            compVarTypeList.extend(cTList)
            subGroupName.extend(sGName)
            cutCodes.extend(cCodes)
            codeRep.extend(cRep)
    elif (typeList[pos] == "cast_expression"):
        rPos, _ = TypeFindFirstInSubTree(pos, ")")
        compVarNameList, compVarTypeList, subGroupName, codeRep, cutCodes = ComplexVarAnalysis(rPos + 1)
    elif (typeList[pos] == "update_expression"):
        _, upAns, cRep, cCodes = updateProcess(pos)
        cutCodes.extend(cCodes)
        codeRep.extend(cRep)
        compVarNameList = upAns.itemList
        compVarTypeList = upAns.itemTypeList
        subGroupName = upAns.bList
    if (compVarNameList == [] and typeList[pos] not in uselessList):
        print("ComplexVarAnalysis Error: Debug", typeList[pos], tokenList[pos])
    return compVarNameList, compVarTypeList, subGroupName, codeRep, cutCodes
def ArgListAnalysis(startPos, endPos, blanks, IgnoreBinary = True):
    argList = []
    addCodeRep = []
    addCodes = []
    i = startPos
    while (i <= endPos):
        if (typeList[i] == "call_expression"):
            funcCall, aCRep, aCodes, fEndPos, _ = FuncSumApply(i, blanks)
            aCodes[-1] = codeAddMark + aCodes[-1]
            addCodeRep.extend(aCRep)
            addCodes.extend(aCodes)
            argList.append(funcCall)
            i = fEndPos + 1
        elif (typeList[i] == "assignment_expression" and i!=startPos):
            lV, rVList, aCRep, aCodes, eqEndPos = AssignAnalysis(i, "")
            addCodeRep.extend(aCRep)
            addCodes.extend(aCodes)
            addCodeRep.append(["assignment", lV, rVList])
            addCodes.append(codeAddMark + tokenList[i])
            argList.append(lV)
            i = eqEndPos + 1
        elif (typeList[i] == "subscript_expression"):
            subEndPos = RangeEndPosFind(i)
            compVarNameList, compVarTypeList, subGroupName, cRep, cCodes = ComplexVarAnalysis(i)
            addCodeRep.extend(cRep)
            addCodes.extend(cCodes)
            imptArg = ArgInfo(compVarNameList, compVarTypeList, subGroupName)
            argList.append(imptArg)
            i = subEndPos + 1
        elif (typeList[i] == "field_expression"):
            subEndPos = RangeEndPosFind(i)
            compVarNameList, compVarTypeList, subGroupName, cRep, cCodes = ComplexVarAnalysis(i)
            addCodeRep.extend(cRep)
            addCodes.extend(cCodes)
            imptArg = ArgInfo(compVarNameList, compVarTypeList, subGroupName)
            addCodes.append(codeAddMark + tokenList[i])
            addCodeRep.append(["Subscript", imptArg, None])
            argList.append(imptArg)
            i = subEndPos + 1
        elif (typeList[i] == "binary_expression" and not IgnoreBinary):
            subEndPos = RangeEndPosFind(i)
            compVarNameList, compVarTypeList, subGroupName, cRep, cCodes = ComplexVarAnalysis(i)
            addCodeRep.extend(cRep)
            addCodes.extend(cCodes)
            imptArg = ArgInfo(compVarNameList, compVarTypeList, subGroupName)
            argList.append(imptArg)
            i = subEndPos + 1
        elif (typeList[i] == "macro_type_specifier"):
            macroTypeEndPos = RangeEndPosFind(i)
            i = macroTypeEndPos + 1
        elif (typeList[i] == "identifier"):
            imptArg = ArgInfo([[tokenList[i]]], [[typeList[i]]], [[tokenList[i]]])
            argList.append(imptArg)
            addCodes.append(codeAddMark + tokenList[i])
            addCodeRep.append(["Subscript", imptArg, None])
            i = i + 1
        elif (typeList[i] in hardCodeType):
            imptArg = ArgInfo([[tokenList[i]]], [[typeList[i]]], [])
            argList.append(imptArg)
            i = i + 1
        else:
            i = i + 1
    return argList, addCodeRep, addCodes
def FuncArgListAnalysis(argListPos, blanks):
    global tokenList
    argList = []
    addCodeRep = []
    addCodes = []
    argListPos = DirectChildrenList(argListPos)
    for sigArgPos in argListPos:
        if (tokenList[sigArgPos] == "," or tokenList[sigArgPos] == "(" or tokenList[sigArgPos] == ")"):
            continue
        if (typeList[sigArgPos] == "call_expression"):
            funcCall, aCRep, aCodes, fEndPos, _ = FuncSumApply(sigArgPos, blanks)
            addCodeAddMark(aCodes)
            aCodes[-1] = codeAddMark + aCodes[-1]
            addCodeRep.extend(aCRep)
            addCodes.extend(aCodes)
            argList.append(funcCall)
        elif (typeList[sigArgPos] == "sizeof_expression"):
            aPos, _ = TypeFindFirstInSubTree(sigArgPos, "parenthesized_expression")
            if (aPos != None):
                ePos = RangeEndPosFind(aPos)
                aL, cRep, cCodes = ArgListAnalysis(aPos, ePos, "")
                addCodeAddMark(cCodes)
                addCodeRep.extend(cRep)
                addCodes.extend(cCodes)
                funcCall = FuncCallInfo("sizeof", None, aL, None, None)
                argList.append(funcCall)
            else:
                aPos, _ = TypeFindFirstInSubTree(sigArgPos, "type_descriptor")
                if (aPos == None):
                    ePos = RangeEndPosFind(sigArgPos+1)
                    aL, cRep, cCodes = ArgListAnalysis(sigArgPos+1, ePos, "")
                    addCodeAddMark(cCodes)
                    addCodeRep.extend(cRep)
                    addCodes.extend(cCodes)
                    funcCall = FuncCallInfo("sizeof", None, aL, None, None)
                    argList.append(funcCall)
                else:
                    aL = [ArgInfo([[tokenList[aPos]]], [[typeList[aPos]]], [[tokenList[aPos]]])]
                    funcCall = FuncCallInfo("sizeof", None, aL, None, None)
                    argList.append(funcCall)
        elif (typeList[sigArgPos] == "update_expression"):
            _, upAns, cRep, cCodes = updateProcess(sigArgPos, True)
            addCodeAddMark(cCodes)
            addCodeRep.extend(cRep)
            addCodes.extend(cCodes)
            argList.append(upAns)
        elif (typeList[sigArgPos] == "subscript_expression"):
            compVarNameList, compVarTypeList, subGroupName, cRep, cCodes = ComplexVarAnalysis(sigArgPos)
            addCodeAddMark(cCodes)
            addCodeRep.extend(cRep)
            addCodes.extend(cCodes)
            imptArg = ArgInfo(compVarNameList, compVarTypeList, subGroupName)
            argList.append(imptArg)
        elif (typeList[sigArgPos] == "field_expression"):
            compVarNameList, compVarTypeList, subGroupName, cRep, cCodes = ComplexVarAnalysis(sigArgPos)
            addCodeAddMark(cCodes)
            addCodeRep.extend(cRep)
            addCodes.extend(cCodes)
            imptArg = ArgInfo(compVarNameList, compVarTypeList, subGroupName)
            addCodes.append(codeAddMark + tokenList[sigArgPos])
            addCodeRep.append(["Subscript", imptArg, None])
            argList.append(imptArg)
        elif (typeList[sigArgPos] == "binary_expression" or typeList[sigArgPos] == "pointer_expression" or typeList[sigArgPos] == "parenthesized_expression" or typeList[sigArgPos] == "unary_expression"):
            compVarNameList, compVarTypeList, subGroupName, cRep, cCodes = ComplexVarAnalysis(sigArgPos)
            addCodeAddMark(cCodes)
            addCodeRep.extend(cRep)
            addCodes.extend(cCodes)
            imptArg = ArgInfo(compVarNameList, compVarTypeList, subGroupName)
            argList.append(imptArg)
        elif (typeList[sigArgPos] == "macro_type_specifier"):
            macroTypeEndPos = RangeEndPosFind(sigArgPos)
        elif (typeList[sigArgPos] == "identifier"):
            imptArg = ArgInfo([[tokenList[sigArgPos]]], [[typeList[sigArgPos]]], [[tokenList[sigArgPos]]])
            addCodeRep.append(["Subscript", imptArg, None])
            addCodes.append(codeAddMark + tokenList[sigArgPos])
            argList.append(imptArg)
        elif (typeList[sigArgPos] == "number_literal" or typeList[sigArgPos] == "string_literal" or typeList[sigArgPos] in hardCodeType):
            imptArg = ArgInfo([[tokenList[sigArgPos]]], [[typeList[sigArgPos]]], [])
            argList.append(imptArg)
        elif (typeList[sigArgPos] == "cast_expression"):
            typePos, _ = TypeFindFirstInSubTree(sigArgPos, "type_descriptor")
            idPos, _ = TypeFindFirstInSubTree(sigArgPos, "identifier")
            if (typePos == None or idPos == None):
                argList.append(None)
            else:
                imptArg = ArgInfo([[tokenList[idPos]]], [[typeList[idPos]]], [[tokenList[sigArgPos]]])
        else:
            ulessList = ["comment", "concatenated_string", "conditional_expression"]
            argList.append(None)
            if (typeList[sigArgPos] not in ulessList):
                print("FuncArgListAnalysis error, not processed:", tokenList[sigArgPos], typeList[sigArgPos])
    return argList, addCodeRep, addCodes
zeroArg = ArgInfo([["0"]], [["number_literal"]], [])
def updateProcess(nodePos, needAddFlag = False):
    cList = DirectChildrenList(nodePos)
    if (len(cList) != 2):
        print("Debug Error:update_expression wrong num", cList)
        for sc in cList:
            print("Detail Error Node:", tokenList[sc], typeList[sc])
        return True, None, [], []
    else:
        if (tokenList[cList[0]] == "++" or tokenList[cList[0]] == "--"):
            compVarNameList, compVarTypeList, subGroupName, cRep, cCodes = ComplexVarAnalysis(cList[1])
            addCodeAddMark(cCodes)
            upAns = ArgInfo(compVarNameList, compVarTypeList, subGroupName)
            cRep.append(["update", upAns])
            if (needAddFlag):
                cCodes.append(codeAddMark + tokenList[nodePos])
            else:
                cCodes.append(tokenList[nodePos])
            return True, upAns, cRep, cCodes
        elif (tokenList[cList[1]] == "++" or tokenList[cList[1]] == "--"):
            compVarNameList, compVarTypeList, subGroupName, cRep, cCodes = ComplexVarAnalysis(cList[0])
            addCodeAddMark(cCodes)
            upAns = ArgInfo(compVarNameList, compVarTypeList, subGroupName)
            cRep.append(["update", upAns])
            if (needAddFlag):
                cCodes.append(codeAddMark + tokenList[nodePos])
            else:
                cCodes.append(tokenList[nodePos])
            return False, upAns, cRep, cCodes
        else:
            print("Debug Error:update_expression wrong token", tokenList[cList[0]], typeList[cList[0]])
            return True, None, [], []

def BranchArgListAnalysis(nodePos):
    global guardSigList, hardCodeType
    if (typeList[nodePos] == "subscript_expression" or typeList[nodePos] == "field_expression"):
        compVarNameList, compVarTypeList, subGroupName, cRep, cCodes = ComplexVarAnalysis(nodePos)
        ans = ArgInfo(compVarNameList, compVarTypeList, subGroupName)
        return ans, subGroupName, False, cRep, cCodes
    elif (typeList[nodePos] == "identifier" or typeList[nodePos] == "field_identifier"):
        ans = ArgInfo([[tokenList[nodePos]]], [[typeList[nodePos]]], [[tokenList[nodePos]]])
        return ans, [[tokenList[nodePos]]], False, [], []
    elif (typeList[nodePos] == "update_expression"):
        _, upAns, cRep, cCodes = updateProcess(nodePos, True)
        return upAns, upAns.bList, False, cRep, cCodes
    elif (typeList[nodePos] == "assignment_expression"):
        leftVar, rightVarList, aCRep, aCodes, eqEndPos = AssignAnalysis(nodePos, "")
        aCRep.append(["assignment", leftVar, rightVarList])
        aCodes.append(codeAddMark + tokenList[nodePos])
        return leftVar, leftVar.bList, False, aCRep, aCodes
    elif (typeList[nodePos] in hardCodeType):
        ans = ArgInfo([[tokenList[nodePos]]], [[typeList[nodePos]]], [])
        return ans, [], False, [], []
    elif (typeList[nodePos] == "parenthesized_expression" or typeList[nodePos] == "pointer_expression" or typeList[nodePos] == "argument_list"):
        return BranchArgListAnalysis(nodePos + 2)
    elif (typeList[nodePos] == "call_expression"):
        funcCall, aCRep, aCodes, fEndPos, _ = FuncSumApply(nodePos, "")
        if (funcCall.name in assertNameList):
            aCRep.pop()
            aCodes.pop()
            constrantList, bList, _, _ = assertCodeRep(nodePos)
            aCRep.append(["Assert", constrantList, bList])
            aCodes.append(codeAddMark + tokenList[nodePos])
            return constrantList, bList, True, aCRep, aCodes
        aCodes[-1] = codeAddMark + aCodes[-1]
        return funcCall, funcCall.bList, False, aCRep, aCodes
    elif (typeList[nodePos] == "sizeof_expression"):
        aPos, _ = TypeFindFirstInSubTree(nodePos, "parenthesized_expression")
        if (aPos!=None):
            ePos = RangeEndPosFind(aPos)
            argList, cRep, cCodes = ArgListAnalysis(aPos, ePos, "")

            funcCall = FuncCallInfo("sizeof", None, argList, None, None)
            temptBList = []
            for sigArg in argList:
                temptBList.append(sigArg.bList)
        else:
            aPos, _ = TypeFindFirstInSubTree(nodePos, "type_descriptor")
            if (aPos == None):
                ePos = RangeEndPosFind(nodePos+1)
                argList, cRep, cCodes = ArgListAnalysis(nodePos+1, ePos, "")
                funcCall = FuncCallInfo("sizeof", None, argList, None, None)
                temptBList = []
                for sigArg in argList:
                    temptBList.append(sigArg.bList)
            else:
                argList = [ArgInfo([[tokenList[aPos]]], [[typeList[aPos]]], [[tokenList[aPos]]])]

                funcCall = FuncCallInfo("sizeof", None, argList, None, None)
                temptBList = [ [[tokenList[aPos]]] ]
                cRep = []
                cCodes = []
        return funcCall, temptBList, False, cRep, cCodes
    elif (typeList[nodePos] == "binary_expression" or typeList[nodePos] == "unary_expression"):
        directCList = DirectChildrenList(nodePos)
        tLen = len(directCList)
        for t in range(tLen):
            sigDir = directCList[t]
            if (tokenList[sigDir] == "!"):
                if (tLen != 2):
                    print("processing \! is Wired!", typeList[nodePos])
                return BranchArgListAnalysis(directCList[t + 1])
            if (tokenList[sigDir] == "&&"):
                if (tLen!=3):
                    print("Wired!", typeList[nodePos])

                temptans = BranchArgListAnalysis(directCList[t-1])
                if (temptans == None):
                    return None
                left, leftBList, lFlag, lcRep, lcCode = temptans
                temptans = BranchArgListAnalysis(directCList[t + 1])
                if (temptans == None):
                    return None
                right, rightBList, rFlag, rcRep, rcCode = temptans
                if (lFlag == False):
                    left = [[left, "!=", zeroArg]]
                    leftBList = [leftBList]
                elif(lFlag == None):
                    ansNum = len(left)
                    for i in range(ansNum):
                        left[i] = [left[i], "!=", zeroArg]
                if (rFlag == False):
                    right = [[right, "!=", zeroArg]]
                    rightBList = [rightBList]
                elif(rFlag == None):
                    ansNum = len(right)
                    for i in range(ansNum):
                        right[i] = [right[i], "!=", zeroArg]
                leftNum = len(left)
                rightNum = len(right)
                total = []
                totalBList = []
                for z in range(leftNum):
                    for k in range(rightNum):
                        imptList = []
                        imptList.append(left[z])
                        imptList.append("&&")
                        imptList.append(right[k])
                        total.append(imptList)
                        imptBList = leftBList[z].copy()
                        imptBList.extend(rightBList[k])
                        totalBList.append(imptBList)
                lcRep.extend(rcRep)
                lcCode.extend(rcCode)
                return total, totalBList, True, lcRep, lcCode
            elif (tokenList[sigDir] == "||"):
                if (tLen!=3):
                    print("Wired!", typeList[nodePos])

                temptans = BranchArgListAnalysis(directCList[t - 1])
                if (temptans == None):
                    return None
                left, leftBList, lFlag, lcRep, lcCode = temptans
                temptans = BranchArgListAnalysis(directCList[t + 1])
                if (temptans == None):
                    return None
                right, rightBList, rFlag, rcRep, rcCode = temptans
                imptList = []
                imptBList = []
                if (lFlag == True):
                    imptList.extend(left)
                    imptBList.extend(leftBList)
                elif (lFlag == False):
                    imptList.append([left, "!=", zeroArg])
                    imptBList.append(leftBList)
                else:
                    leftNum = len(left)
                    for sigLeftPos in range(leftNum):
                        imptList.append([left[sigLeftPos], "!=", zeroArg])
                        imptBList.append(leftBList[sigLeftPos])
                if (rFlag == True):
                    imptList.extend(right)
                    imptBList.extend(rightBList)
                elif (rFlag == False):
                    imptList.append([right, "!=", zeroArg])
                    imptBList.append(rightBList)
                else:
                    rightNum = len(right)
                    for sigLeftPos in range(rightNum):
                        imptList.append([right[sigLeftPos], "!=", zeroArg])
                        imptBList.append(rightBList[sigLeftPos])
                lcRep.extend(rcRep)
                lcCode.extend(rcCode)
                return imptList, imptBList, True, lcRep, lcCode
            elif (tokenList[sigDir] in guardSigList[0]):
                temptans = BranchArgListAnalysis(directCList[t - 1])
                if (temptans == None):
                    return None
                left, leftBList, lFlag, lcRep, lcCode = temptans
                temptans = BranchArgListAnalysis(directCList[t + 1])
                if (temptans == None):
                    return None
                right, rightBList, rFlag, rcRep, rcCode = temptans
                if (lFlag == True or rFlag == True):
                    print("Debug Error: This is not suppose to happen")
                    return None
                if (lFlag == None and rFlag == None):
                    lNum = len(left)
                    rNum = len(right)
                    imptList = []
                    imptBList = []
                    for lPos in range(lNum):
                        for rPos in range(rNum):
                            imptList.append([left[lPos], tokenList[sigDir], right[rPos]])
                            tempBList = leftBList[lPos].copy()
                            tempBList.extend(rightBList[rPos])
                            imptBList.append(tempBList)
                    lcRep.extend(rcRep)
                    lcCode.extend(rcCode)
                    return imptList, imptBList, True, lcRep, lcCode
                elif (lFlag == None):
                    lNum = len(left)
                    imptList = []
                    imptBList = []
                    for lPos in range(lNum):
                        imptList.append([left[lPos], tokenList[sigDir], right])
                        tempBList = leftBList[lPos].copy()
                        tempBList.extend(rightBList)
                        imptBList.append(tempBList)
                    lcRep.extend(rcRep)
                    lcCode.extend(rcCode)
                    return imptList, imptBList, True, lcRep, lcCode
                elif (rFlag == None):
                    rNum = len(right)
                    imptList = []
                    imptBList = []
                    for rPos in range(rNum):
                        imptList.append([left, tokenList[sigDir], right[rPos]])
                        tempBList = leftBList.copy()
                        tempBList.extend(rightBList[rPos])
                        imptBList.append(tempBList)
                    lcRep.extend(rcRep)
                    lcCode.extend(rcCode)
                    return imptList, imptBList, True, lcRep, lcCode
                else:
                    imptList = [[left, tokenList[sigDir], right]]
                    imptBList = leftBList.copy()
                    imptBList.extend(rightBList)
                    imptBList = [imptBList]
                    lcRep.extend(rcRep)
                    lcCode.extend(rcCode)
                    return imptList, imptBList, True, lcRep, lcCode
        compVarNameList, compVarTypeList, subGroupName, cRep, cCodes = ComplexVarAnalysis(nodePos)
        ans = ArgInfo(compVarNameList, compVarTypeList, subGroupName)
        cRep.append(["Subscript", ans, None])
        cCodes.append(codeAddMark + tokenList[nodePos])
        return ans, subGroupName, False, cRep, cCodes
    elif (typeList[nodePos] == "cast_expression"):
        typePos, _ = TypeFindFirstInSubTree(nodePos, "type_descriptor")
        idPos, _ = TypeFindFirstInSubTree(nodePos, "identifier")
        if (typePos == None or idPos == None):
            return None
        else:
            return BranchArgListAnalysis(idPos)
    else:
        uselessTypeList = ["comment"]
        if (typeList[nodePos] not in uselessTypeList):
            print("DebugError BranchArgListAnalysis: This is not expected", tokenList[nodePos], typeList[nodePos])
            cList = ChildrenList(nodePos)
            for scL in cList:
                print("Containing Children", tokenList[scL], typeList[scL])
        return None

def gotoCodeRep(nodePos):
    gotoIDPos, gotoEndPos = TypeFindFirstInSubTree(nodePos, "statement_identifier")
    return tokenList[gotoIDPos], gotoEndPos
def addListReform(addList, move):
    for sigItem in addList:
        sigItem[0] = sigItem[0] + move
        sigItem[1] = sigItem[1] + move
assertNameList = ["assert", "unlikely", "WARN_ON", "WARN_ON_ONCE"]
def CodeBlockAnalysis(startPos, endPos, blanks, codesNum):
    global assertNameList
    Codes = []
    CodeRepList = []
    i = startPos
    ContainErrorLog = False
    goto_flag = False
    while (i <= endPos):
        if (typeList[i] == "declaration"):
            tempt = DeclarProcess(i, blanks)
            if (not isinstance(tempt, int)):
                _, createdVarList, createdVarType, leftVarList, rightVarListList, aCRep, aCodes, declarEndPos = tempt
                CodeRepList.extend(aCRep)
                Codes.extend(aCodes)
                CodeRepList.append(["declartion", createdVarList, createdVarType, leftVarList, rightVarListList])
                Codes.append(tokenList[i])
                i = declarEndPos + 1
            else:
                i = tempt+1
        elif (typeList[i] == "assignment_expression"):
            leftVar, rightVarList, aCRep, aCodes, eqEndPos = AssignAnalysis(i, blanks)
            CodeRepList.extend(aCRep)
            Codes.extend(aCodes)
            CodeRepList.append(["assignment", leftVar, rightVarList])
            Codes.append(blanks + tokenList[i])
            i = eqEndPos + 1
        elif (typeList[i] == "update_expression"):
            _, upAns, cRep, cCodes = updateProcess(i)
            CodeRepList.extend(cRep)
            Codes.extend(cCodes)
            i = i + 1
        elif (typeList[i] == "case_statement"):
            CodeRepList.append(["case_statement"])
            splitP = tokenList[i].find(":")
            Codes.append(blanks + tokenList[i][:splitP])
            i = i + 1
        elif (typeList[i] == "call_expression"):
            funcCall, aCRep, aCodes, callEndPos, ELFlag = FuncSumApply(i, blanks)
            if (funcCall.name in assertNameList):
                constrantList, bList, aCRep, aCodes = assertCodeRep(i)
                CodeRepList.extend(aCRep)
                Codes.extend(aCodes)
                CodeRepList.append(["Assert", constrantList, bList])
                Codes.append(tokenList[i])
                i = callEndPos + 1
            else:
                if (ELFlag == 1):
                    ContainErrorLog = True
                CodeRepList.extend(aCRep)
                Codes.extend(aCodes)
                i = callEndPos + 1
        elif (typeList[i] == "if_statement"):
            elseExistFlag, branchVarList, constrantList, bList, guardPos, ifCodes, ifCodeRepList, elseCodes, elseCodeRepList, branchEndPos, aCRep, aCodes = ifCodeRep(i, blanks, codesNum+len(Codes))
            s = len(Codes) + codesNum
            Codes.extend(aCodes)
            guards = len(Codes) + codesNum
            Codes.append("if " + tokenList[guardPos])
            Codes.extend(ifCodes)
            e = len(Codes) + codesNum
            es = -1
            ee = -1
            if(elseExistFlag):
                es = len(Codes) + codesNum
                Codes.append(blanks + "else")
                Codes.extend(elseCodes)
                ee = len(Codes) + codesNum
            CodeRepList.extend(aCRep)
            CodeRepList.append(["if_statement", elseExistFlag, s, guards, e, es, ee, branchVarList, constrantList, bList])
            CodeRepList.extend(ifCodeRepList)
            if (elseExistFlag):
                CodeRepList.append(["else_statement", [[]]])
                CodeRepList.extend(elseCodeRepList)
            i = branchEndPos + 1
        elif (typeList[i] == "switch_statement"):
            branchVarList, constrantList, bList, guardPos, switchCodes, switchCodeRepList, branchEndPos, aCRep, aCodes = switchCodeRep(i, blanks, codesNum+len(Codes))
            s = len(Codes) + codesNum
            Codes.extend(aCodes)
            gs = len(Codes) + codesNum
            Codes.append(blanks + "switch " + tokenList[guardPos])
            Codes.extend(switchCodes)
            endP = len(Codes) + codesNum
            CodeRepList.extend(aCRep)
            CodeRepList.append(["switch_statement", s, gs, endP, branchVarList, constrantList, bList])
            CodeRepList.extend(switchCodeRepList)
            i = branchEndPos + 1
        elif (typeList[i] == "while_statement" or typeList[i] == "do_statement"):
            branchVarList, constrantList, bList, guardPos, whileCodes, whileCodeRepList, branchEndPos, aCRep, aCodes = whileCodeRep(i, blanks, codesNum+len(Codes))
            s = len(Codes) + codesNum
            Codes.extend(aCodes)
            gs = len(Codes) + codesNum
            if (typeList[i] == "while_statement"):
                Codes.append(blanks + "while " + tokenList[guardPos])
            else:
                Codes.append(blanks + "do " + tokenList[guardPos])
            Codes.extend(whileCodes)
            endP = len(Codes) + codesNum
            CodeRepList.extend(aCRep)
            CodeRepList.append(["while_statement", s, gs, endP, branchVarList, constrantList, bList])
            CodeRepList.extend(whileCodeRepList)
            i = branchEndPos + 1
        elif (typeList[i] == "goto_statement"):
            gotoID, gotoEndPos = gotoCodeRep(i)
            goto_flag = True
            CodeRepList.append(["goto_statement", gotoID])
            Codes.append(blanks + tokenList[i])
            i = gotoEndPos + 1
        elif (typeList[i] == "statement_identifier"):
            CodeRepList.append(["statementID", tokenList[i]])
            Codes.append(blanks + tokenList[i])
            i = i + 1
        elif (typeList[i] == "return_statement"):
            argList, aCRep, aCodes, returnEndPos = returnCodeRep(i, blanks)
            CodeRepList.extend(aCRep)
            Codes.extend(aCodes)
            CodeRepList.append(["return_statement", argList])
            Codes.append(blanks + tokenList[i])
            i = returnEndPos + 1
        else:
            i = i + 1
    return Codes, CodeRepList, ContainErrorLog, goto_flag
def ReturnCounter():
    global codes, codeRepList, resRepGlobList
    cNum = len(codes)
    ansPosList = []
    for i in range(cNum):
        if (codeRepList[i][0] == "return_statement"):
            ansPosList.append(i)
    return ansPosList
def returnBListGen(argList, argPos):
    if (argList!=[] and argList[0].bList!=[]):
        return argList[0].bList
    else:
        return [["*__Empty Return__*"+str(argPos)]]
def returnRRListModified(returnRRList, returnArgBList):
    rRNum = len(returnRRList)
    for i in range(rRNum):
        if (returnRRList[i][0]!="Need Extend"):
            returnRRList[i][-1].extend(returnArgBList)
valuableRR = ["Assign", "FuncCall","CHECK"]
def BListMatch(resRepBList, bList):
    for sigbased in bList:
        if (InBasedList(resRepBList, sigbased)):
            return True
    return False
def BListListMatch(resRepBList, bListList):
    for sigbList in bListList:
        if (BListMatch(resRepBList, sigbList)):
            return True
    return False
def BListsMatch(resRepBList, bLists):
    n = len(bLists)
    ansList = []
    for i in range(n):
        if (BListMatch(resRepBList, bLists[i])):
            ansList.append(i)
    return ansList
globalSortedList = []
def PosListSort(posList, resrepList):
    global globalSortedList, resRepGlobListFlat
    indexList = []
    posNum = len(posList)
    if (posNum!=len(resrepList)):
        print("Debug Error, PosListSort Len not match")
    if (posList == []):
        return [], []
    ans = []
    ansResrep = []
    gNum = len(globalSortedList)
    needExtendFlag = False
    if (posList[0] == None):
        needExtendFlag = True
    for i in range(gNum):
        if (globalSortedList[i] in posList):
            ans.append(globalSortedList[i])
            ansResrep.append(resrepList[posList.index(globalSortedList[i])])
            indexList.append(resRepGlobListFlat[globalSortedList[i]])
            if (len(ans) == posNum):
                break
    if (needExtendFlag):
        ans.insert(0, None)
        ansResrep.insert(0, resrepList[0])
        indexList.insert(0, None)
    return ans, ansResrep, indexList
def MulBListMatch(totalBList, sigresrepBList):
    for sigArgBased in totalBList:
        for sigB in sigArgBased:
            if (InBasedList(sigresrepBList, sigB)):
                return True
    return False
def NeedExtendCheck(uperList, uperPosList, totalBListList, TrackThreshold, funcArgInfo):
    num = len(uperList)
    if (num != len(uperPosList) or num != len(totalBListList)):
        print("Debug Error NeedExtendCheck, Length not match")
    for i in range(num):
        SigNeedExtendCheck(TrackThreshold, funcArgInfo, totalBListList[i], uperList[i], uperPosList[i])

def SigNeedExtendCheck(TrackThreshold, funcArgInfo, totalBList, ansRR, ansPos):
    findedTrack = len(ansRR)
    if (findedTrack < TrackThreshold):
        extendList = []
        funcArgNum = len(funcArgInfo)
        for jjk in range(funcArgNum):
            sigArg = funcArgInfo[jjk]
            for sigReturnBased in totalBList:
                argAdded = False
                for sigItem in sigReturnBased:
                    if (sigArg[1] in sigItem):

                        extendList.append(jjk)
                        findedTrack = findedTrack + 1
                        argAdded = True
                        break
                if (argAdded):
                    break
            if (extendList != []):
                if (ansRR == [] or ansRR[0][0] != "Need Extend"):
                    ansRR.insert(0, ["Need Extend", extendList])
                    ansPos.insert(0, None)
                else:
                    for sigE in extendList:
                        if sigE not in ansRR[0][1]:
                            ansRR[0][1].append(sigE)
def ConcatList(ansRR, ansPos, ansIndex, rrList, posList, indexList):
    num = len(rrList)
    for i in range(num):
        rrList[i].extend(ansRR)
        posList[i].extend(ansPos)
        indexList[i].extend(ansIndex)
emptyReturn = ArgInfo([["*__EmptyReturn__*"]], [["Var"]], [["*__EmptyReturn__*"]])
def meteralDivide(constrainAndContext, funcName):
    global studyMeteral
    funcMet = []
    for sigC in constrainAndContext:
        if (sigC.upDataList!=[] and sigC.upDataList[0] == None):
            funcMet.append(sigC)
        else:
            AddNewMeteral(sigC, "MeteralDivide"+funcName)
    return funcMet
def AddNewMeteral(a, sourceMark):
    global studyMeteral, studyMeteralSource
    studyMeteral.append(a)
    studyMeteralSource.append(sourceMark)
resRepMapInfo = []
resRepRudu = []
data2RR = []
dataList = []
def LinkResRep(a, b):
    global resRepGlobList, data2RR

    aLen = len(resRepGlobList[a])
    bLen = len(resRepGlobList[b])
    aoffset = data2RR[a]
    boffset = data2RR[b]
    for ai in range(aLen):
        AddEdges(aoffset+ai, list(range(boffset, boffset+bLen)))

def AddResLink(s,e, target):
    for i in range(s, e+1):
        LinkResRep(i, target)
def BranchLink(target, s, e):
    for i in range(s, e+1):
        if (i == target):
            continue
        LinkResRep(target, i)
def AddEdge(a,b):
    global resRepMapInfo, resRepRudu
    if (a != b):
        resRepMapInfo[a].append(b)
        resRepRudu[b].append(a)
def AddEdges(a, bList):
    global resRepMapInfo, resRepRudu
    resRepMapInfo[a].extend(bList)
    for sigb in bList:
        resRepRudu[sigb].append(a)
def AddCount(curcode):
    global codeAddMark
    tempt = curcode
    cl = len(codeAddMark)
    counter = 0
    while (codeAddMark in tempt):
        counter += 1
        tempt = tempt[cl:]
    return counter
def AddCodesMapProcess(pos, num):
    global codes, codeRepList, resRepGlobList, data2RR, resRepGlobListFlat
    curCount = AddCount(codes[pos])
    e = pos + 1
    while (e < num and codes[e][:len(codeAddMark)] == codeAddMark and AddCount(codes[e])==curCount):
        e = e + 1
    if (codeRepList[e][0] == "if_statement" or codeRepList[e][0] == "while_statement" or codeRepList[e][0] == "switch_statement" or codeRepList[e][0] =="Assert"):
        cBLists = []
        cpList = []
        sigrrn = len(resRepGlobList[e])
        for s in range(sigrrn):
            if (resRepGlobList[e][s][0] == "CHECK"):
                cBLists.append(resRepGlobList[e][s][-1])
                cpList.append(data2RR[e]+s)
        for curi in range(pos, e):
            errNum = len(resRepGlobList[curi])
            for curj in range(errNum):
                cPs = data2RR[curi]+curj
                if (resRepGlobList[curi][curj][0] == "FuncCall"):
                    matchList = []
                    for sigrr in resRepGlobList[curi][curj][-1]:
                        mList = BListsMatch(sigrr, cBLists)
                        matchList.extend(mList)
                    for sigMatch in matchList:
                        AddEdge(cPs, cpList[sigMatch])
                else:
                    matchList = BListsMatch(resRepGlobList[curi][curj][-1], cBLists)
                    for sigMatch in matchList:
                        AddEdge(cPs, cpList[sigMatch])
    else:
        AddResLink(pos, e-1, e)
    return e
def IfElseLink(gs, se):
    global data2RR, resRepGlobListFlat
    s = data2RR[gs+1]-1
    while(resRepGlobListFlat[s][0]=="CHECK"):
        AddEdge(s, data2RR[se+1]-1)
        s = s - 1
def FormMap(argInfo):

    global codes, codeRepList, resRepGlobList, resRepGlobListFlat
    global resRepMapInfo, resRepRudu, data2RR, PickList, ifElseList
    global globalContext
    ifElseList = []
    argNum = len(argInfo)
    BLists = []
    posList = []
    resMapNum = len(resRepGlobListFlat)
    for i in range(argNum):
        BLists.append([[argInfo[i][1]]])
        posList.append(resMapNum+argNum -1 - i)
    resRepMapInfo = [[] for _ in range(resMapNum+argNum)]
    resRepRudu = [[] for _ in range(resMapNum+argNum)]
    PickList = [None for _ in range(resMapNum+argNum)]
    if (len(codes)!=len(codeRepList)):
        print("Not Match!", len(codes), len(codeRepList))
    num = len(codes)
    DataTrack(0, num-1, num, BLists, posList)
    EdgeDupReduce(resMapNum)
def EdgeDupReduce(resMapNum):
    global resRepMapInfo, resRepRudu
    rNum = len(resRepMapInfo)
    for sigrrm in range(rNum):
        resRepMapInfo[sigrrm] = list(set(resRepMapInfo[sigrrm]))
        resRepRudu[sigrrm] = list(set(resRepRudu[sigrrm]))
        resRepMapInfo[sigrrm].sort()
        curN = len(resRepMapInfo[sigrrm])
        for i in range(curN):
            if (resRepMapInfo[sigrrm][i]>=resMapNum):
                resRepMapInfo[sigrrm] = resRepMapInfo[sigrrm][i:]+resRepMapInfo[sigrrm][:i]
def BListCombine(bList1, bList2):
    newBList = []
    for i in bList1:
        if i not in bList2:
            newBList.append(i)
    newBList.extend(bList2)
    return newBList
def Replaceable(posa, codePosb):
    global codeLevel, data2RR, resRepGlobList
    rrNum = len(resRepGlobListFlat)
    if (posa>=rrNum):
        if (codeLevel[codePosb] == 0):
            return True
        return False
    codePosa = 0
    while (data2RR[codePosa] <= posa):
        codePosa += 1
    codePosa -= 1
    if (codePosa == codePosb):
        return False
    minx = min(codeLevel[codePosa:codePosb])
    if (minx<codeLevel[codePosb]):
        return False
    if (codeLevel[codePosa]>=codeLevel[codePosb]):
        return True
    return False
PickList = []
ifElseList = []
def DataTrack(s, e, num, BLists, posList):
    global codes, codeRepList, resRepGlobList, resRepGlobListFlat
    global resRepMapInfo, resRepRudu, data2RR
    global PickList, ifElseList
    i = s
    rflatNum = len(resRepGlobListFlat)
    while (i <= e):
        rNum = len(resRepGlobList[i])
        offset = data2RR[i]
        blankNum = 0
        for j in range(rNum):
            if (resRepGlobList[i][j] == []):
                blankNum += 1
                continue
            if (resRepGlobList[i][j][0] == "else_statement"):
                continue
            curPos = offset + j
            if (resRepGlobList[i][j][0] == "FuncCall"):
                fCall = resRepGlobList[i][j][1]
                if (fCall.argList == None or fCall.bList == []):
                    continue
                argNum = len(fCall.argList)
                pickedList = []
                addrList = fCall.addressList
                for sigarg in range(argNum):
                    mList = BListsMatch(resRepGlobList[i][j][-1][sigarg], BLists)
                    if (mList!=[]):
                        for sigm in mList:
                            pickedList.append([posList[sigm], sigarg])
                        for sm in mList:
                            AddEdge(posList[sm], curPos)
                        for sm in mList:
                            if (Replaceable(posList[sm], i)):
                                posList[sm] = curPos
                    if (curPos not in posList and resRepGlobList[i][j][-1][sigarg] not in BLists):
                        BLists.append(resRepGlobList[i][j][-1][sigarg])
                        posList.append(curPos)
                for sigP in pickedList:
                    if (PickList[curPos]==None):
                        PickList[curPos] = [[sigP[0], [sigP[1]]]]
                    else:
                        pNum = len(PickList[curPos])
                        fFlag = False
                        for pn in range(pNum):
                            if (PickList[curPos][pn][0] == sigP[0] and sigP[1] not in PickList[curPos][pn][1]):
                                PickList[curPos][pn][1].append(sigP[1])
                                fFlag = True
                                break
                        if (not fFlag):
                            PickList[curPos].append([sigP[0], [sigP[1]]])
                continue
            matchList = BListsMatch(resRepGlobList[i][j][-1], BLists)
            if (resRepGlobList[i][j][0] == "Create" or resRepGlobList[i][j][0] == "Assign"):
                if (matchList!=[]):
                    for sm in matchList:
                        if(posList[sm]<rflatNum and resRepGlobListFlat[posList[sm]][0]!="CHECK"):
                            if (Replaceable(posList[sm], i)):
                                posList[sm] = curPos
                if (curPos not in posList):
                    BLists.append(resRepGlobList[i][j][-1])
                    posList.append(curPos)
            elif (resRepGlobList[i][j][0] == "CHECK"):
                if (matchList!=[]):
                    for sm in matchList:
                        AddEdge(posList[sm], curPos)
                        if (posList[sm]<rflatNum):
                            if (resRepGlobListFlat[posList[sm]][0]!="CHECK"):
                                if(not (j+1<rNum and resRepGlobList[i][j][0] == "CHECK") or (posList[sm]>=offset)):
                                    if (Replaceable(posList[sm], i)):
                                        posList[sm] = curPos
                        else:
                            if (not (j + 1 < rNum and resRepGlobList[i][j][0] == "CHECK") or (posList[sm] >= offset)):
                                if (Replaceable(posList[sm], i)):
                                    posList[sm] = curPos
                if (curPos not in posList):
                    BLists.append(resRepGlobList[i][j][-1])
                    posList.append(curPos)
            elif (resRepGlobList[i][j][0] == "Read" and resRepGlobList[i][j][2]!=None):
                if (matchList!=[]):
                    for sm in matchList:
                        AddEdge(posList[sm], curPos)
                        if (Replaceable(posList[sm], i)):
                            posList[sm] = curPos
            else:
                for sigMatch in matchList:
                    AddEdge(posList[sigMatch], curPos)
        if (codes[i][:len(codeAddMark)] == codeAddMark):
            AddCodesMapProcess(i, num)
            i = i + 1
            continue
        if (codeRepList[i][0] == "if_statement"):
            _, elseExistFlag, s, gs, branchEndPos, se, elseEndPos, branchVarList, constrantList, bList = codeRepList[i]
            if (i != gs):
                print("FormMap Debug Error: i and gs not match")
            BranchLink(gs, gs + 1, branchEndPos - 1)
            ed = gs
            if (elseExistFlag):
                ifElseList.append([s, gs, branchEndPos, se, elseEndPos])
                IfElseLink(gs, se)
                BranchLink(se, se + 1, elseEndPos - 1)
                ifBList, ifPosList = DataTrack(gs + 1, branchEndPos - 1, num, BLists, posList)
                elseBList, elsePosList = DataTrack(se + 1, elseEndPos - 1, num, BLists, posList)
                BLists = BListCombine(ifBList, elseBList)
                posList = BListCombine(ifPosList, elsePosList)
                ed = elseEndPos
            i = ed + 1
            continue
        elif (codeRepList[i][0] == "while_statement"):
            _, s, gs, branchEndPos, branchVarList, constrantList, bList = codeRepList[i]
            BranchLink(gs, gs+1, branchEndPos-1)
            i = i + 1
        elif (codeRepList[i][0] == "switch_statement"):
            _, s, gs, branchEndPos, branchVarList, constrantList, bList = codeRepList[i]
            BranchLink(gs, gs+1, branchEndPos-1)
            i = i + 1
        else:
            i += 1
    return BLists, posList
def dataSortRule(a, b):
    return a[1]<b[1]
def sortSelectedList(selectedList):
    global dataList, rrDataGlobListFlat, codes, PickList
    rN = len(rrDataGlobListFlat)
    pN = len(PickList)
    if (selectedList == []):
        return []
    imptList = []
    needExtendFlag = False
    if (selectedList[0] == None):
        needExtendFlag = True
        selectedList = selectedList[1:]
    for i in selectedList:
        if (i>=rN):
            imptList.append([i, rN-i])
        else:
            imptList.append([i, dataList[i]])
    sorted(imptList, key=functools.cmp_to_key(dataSortRule))
    ans = []
    for i in imptList:
        ans.append(i[0])
    if (needExtendFlag):
        ans.insert(0, None)
    return ans
def RuduSelect(chuduList, ruduList):
    num = len(ruduList)
    needProcessList = [i for i in range(num)]
    ans = []
    while(1):
        waitSortList = []
        for i in needProcessList:
            if (ruduList[i] == []):
                waitSortList.append(i)
                for sigTarget in chuduList[i]:
                    if (i in ruduList[sigTarget]):
                        ruduList[sigTarget].remove(i)
        ans.extend(sortSelectedList(waitSortList))
        for i in waitSortList:
            needProcessList.remove(i)
        if (waitSortList == []):
            break
    if (needProcessList!=[]):
        print("RuduSelect Wrong!!!!!")
    return ans
def TopSort(chuduList, ruduList):
    global resRepMapInfo, resRepRudu
    ans = RuduSelect(copy.deepcopy(chuduList), copy.deepcopy(ruduList))
    return ans
def CheckTrace():
    global resRepGlobList, resRepGlobListFlat, resRepRudu, rrDataGlobListFlat, data2RR, resRepMapInfo, AssignDict
    rflatNum = len(resRepGlobListFlat)
    cNum = len(resRepGlobList)
    for i in range(cNum):
        rn = len(resRepGlobList[i])
        offset = data2RR[i]
        for j in range(rn):
            curPos = offset+j
            if (resRepGlobListFlat[curPos][0] == "Assign"):
                _, _, _, left, rightList, _ = resRepGlobListFlat[curPos]
                if (len(rightList) == 1):
                    if (rightList[0].norm == [["__HardCodedVar__"]]):
                        continue
                    k = BList2String(left.bList)
                    AssignDict = {}
                    AssignDict[k] = rightList[0]
                    chuNum = len(resRepMapInfo[curPos])
                    for k in range(chuNum):
                        targetPos = resRepMapInfo[curPos][k]
                        if (resRepGlobListFlat[targetPos][0] == "CHECK" or resRepGlobListFlat[targetPos][0] == "Assert CHECK"):
                            nCL = []
                            ncons = []
                            for sigc in resRepGlobListFlat[targetPos][2]:
                                nc = ConstrainReplace(sigc)
                                nCL.append(nc)
                                cnl, _ = ConstrantNormalize(nc)
                                ncons.append(cnl)
                            resRepGlobListFlat[targetPos][2] = nCL
                            resRepGlobListFlat[targetPos][1] = ncons
                            resRepGlobList[i][j] = resRepGlobListFlat[targetPos]
                            pos = addGlobalContext([], showConstrain(resRepGlobListFlat[targetPos][1]), resRepGlobListFlat[targetPos])
                            rrDataGlobListFlat[targetPos] = pos
                        elif (resRepGlobListFlat[targetPos][0] == "Read"):
                            tempt = AssignMatch(resRepGlobListFlat[targetPos][3], True)
                            if (tempt!=None):
                                resRepGlobListFlat[targetPos][3] = tempt
                                resRepGlobListFlat[targetPos][1] = tempt.norm
                            if (resRepGlobListFlat[targetPos][4]!=None):
                                tempt = AssignMatch(resRepGlobListFlat[targetPos][4], True)
                                if (tempt != None):
                                    resRepGlobListFlat[targetPos][4] = tempt
                                    resRepGlobListFlat[targetPos][2] = tempt.norm
                            resRepGlobList[i][j] = resRepGlobListFlat[targetPos]
                            tempt = MulList2str(resRepGlobListFlat[targetPos][:-3])
                            pos = addGlobalContext([], tempt, resRepGlobListFlat[targetPos])
                            rrDataGlobListFlat[targetPos] = pos
                        elif (resRepGlobListFlat[targetPos][0] == "Return"):
                            newaList = []
                            for siga in resRepGlobListFlat[targetPos][1]:
                                tempt = AssignMatch(siga, True)
                                if (tempt !=None):
                                    newaList.append(tempt)
                                else:
                                    newaList.append(siga)
                            resRepGlobListFlat[targetPos][1] = newaList
                            resRepGlobList[i][j] = resRepGlobListFlat[targetPos]
                            tempt = MulList2str(resRepGlobList[i][j])
                            pos = addGlobalContext([], tempt, resRepGlobList[i][j])
                            rrDataGlobListFlat[targetPos] = pos
def ReturnMarkSet(returnControlList, returnMarkList):
    global EHBranch, codeRepList, data2RR
    returnNum = len(returnControlList)
    for i in range(returnNum):
        for sigs, sige in EHBranch:
            if (sigs<returnControlList[i] and returnControlList[i]<sige and returnMarkList ==0):
                returnMarkList[i] = -1
    return returnControlList, returnMarkList
funcBackGround = {}
codeLevel = []
def FuncDetailInfoTrace(filePos, nodePos, funcName, funcType):
    global codes, codeRepList, resRepGlobList, resRepGlobListFlat, rrDataGlobListFlat
    global structTypeName, funcDefSumDict
    global defedVarNameList, defedVarTypeList
    global data2RR, dataList, globalSortedList, BranchEHMark
    global funcTypeDict
    global EHBranch
    global codeLevel
    global resRepMapInfo
    defedVarNameList = []
    defedVarTypeList = []
    EHBranch = []
    argInfo, ePos, addressList = ParaAnalysis(nodePos)
    if (argInfo == None):
        return None
    decPos, _ = TypeFindFirstInSubTree(nodePos, "function_declarator")
    if (decPos == None):
        return None
    rPos = RangeEndPosFind(decPos)
    blanks = ""
    codes, codeRepList, _, goto_flag = CodeBlockAnalysis(rPos+1, ePos, blanks, 0)
    crNum = len(codeRepList)
    if (len(codes)!= crNum):
        print("Debug Error: codes and codeRepList num not match!")
        return None
    if (goto_flag):
        GotoHandle()
    resRepGlobList = []
    resRepGlobListFlat = []
    rrDataGlobListFlat = []
    funcExtendThreshold = 2
    crNum = len(codeRepList)
    codeLevel = [0 for _ in range(crNum)]
    errorPosList, errorLogArgListList, dataList, jumpList = CodeRep2ResRep(funcName, argInfo, funcExtendThreshold)
    if (len(resRepGlobList)!=len(codes)):
        print("Debug Error: CodeRep2ResRep resRepGlobList and codes num not match!", len(codes), len(resRepGlobList))
    FormMap(argInfo)
    argN = len(argInfo)
    chuduList = []
    ruduList = []
    if (argN!=0):
        chuduList = copy.deepcopy(resRepMapInfo)
        ruduList = copy.deepcopy(resRepRudu)
    else:
        chuduList = copy.deepcopy(resRepMapInfo)
        ruduList = copy.deepcopy(resRepRudu)
    if (len(chuduList)>300):
        return None
    globalSortedList = TopSort(chuduList, ruduList)
    CheckTrace()
    BranchEHMark = []
    imptC, moreRPosList = EHProcess(errorPosList, argInfo)
    imptC2, _ = EHProcess(moreRPosList, argInfo)
    imptC.extend(imptC2)
    imptC = meteralDivide(imptC, funcName)
    if (len(imptC)>1):
        print("len(imptC)>1", funcName)
    EHContentStudy()
    FuncContext(funcName)
    argPosLists = ArgTrace()
    returnList, returnControlList, returnMarkList = returnTrace()
    returnControlList, returnMarkList = ReturnMarkSet(returnControlList, returnMarkList)
    funcDefSumDict[funcName] = [funcType, copy.deepcopy(argInfo), \
                                copy.deepcopy(addressList), \
                                copy.deepcopy(argPosLists), \
                                copy.deepcopy(returnList), \
                                copy.deepcopy(returnControlList), \
                                copy.deepcopy(returnMarkList), \
                                copy.deepcopy(imptC), \
                                copy.deepcopy(resRepGlobListFlat), \
                                copy.deepcopy(rrDataGlobListFlat), \
                                copy.deepcopy(jumpList),\
                                copy.deepcopy(resRepMapInfo),
                                copy.deepcopy(defedVarTypeList)
                                ]
    funcBackGround[funcName] = [
        copy.deepcopy(codes),\
        copy.deepcopy(codeRepList),\
        copy.deepcopy(resRepGlobList),\
        copy.deepcopy(resRepGlobListFlat),\
        copy.deepcopy(rrDataGlobListFlat),\
        copy.deepcopy(data2RR),\
        copy.deepcopy(resRepMapInfo), \
        copy.deepcopy(resRepRudu), \
        copy.deepcopy(PickList),\
        copy.deepcopy(BranchEHMark), \
        copy.deepcopy(EHBranch)
    ]

EHContentReturn = {}
EHContentFuncCall = {}
TotalContentReturn = {}
def EHContentStudy():
    global EHBranch, resRepGlobList, EHContentReturn, EHContentFuncCall, resRepGlobListFlat
    for s, e in EHBranch:
        for i in range(s, e):
            for sigrr in resRepGlobList[i]:
                if (sigrr[0] == "FuncCall"):
                    curFuncName = sigrr[1].name
                    if (curFuncName not in EHContentFuncCall):
                        EHContentFuncCall[curFuncName] = 1
                    else:
                        EHContentFuncCall[curFuncName] += 1
                elif (sigrr[0] == "Return"):
                    aList = sigrr[1]
                    if(len(aList)!=1):
                        continue
                    sigRetArg = aList[0]
                    if (sigRetArg.norm == [["__HardCodedVar__"]]):
                        temptStr = BList2String(sigRetArg.bList)
                        if (temptStr not in EHContentReturn):
                            EHContentReturn[temptStr] = 1
                        else:
                            EHContentReturn[temptStr] += 1
def BList2String(bList):
    ansList = []
    for sigb in bList:
        ansList.append(" ".join(sigb))
    return " ".join(ansList)
AssignDict = {}
funcContextDict = {}
def FuncContext(funcName):
    global resRepGlobListFlat, rrDataGlobListFlat, PickList, codeRepList
    rNum = len(resRepGlobListFlat)
    pNum = len(PickList)
    cNum = len(codeRepList)
    for i in range(rNum):
        if (resRepGlobListFlat[i][0] == "FuncCall"):
            fN = resRepGlobListFlat[i][1].name
            cpos = 0
            while(data2RR[cpos]<=i):
                cpos = cpos + 1
            cpos = cpos - 1
            upperRange = list(range(0, cpos))
            upperRange = upperRangeAdjust(upperRange, cpos)
            upperRange.extend(list(range(rNum, pNum)))
            downRange = list(range(i+1, rNum))
            upRR, upData, downRR, downData = BListSearch(upperRange, downRange, [i])
            upData.append(rrDataGlobListFlat[i])
            upData.extend(downData)
            if(upData[0] == None):
                upData[0] = -1
            if (fN not in funcContextDict):
                funcContextDict[fN] = [rrDataGlobListFlat[i], [[funcName, upData.copy()]]]
            else:
                if (rrDataGlobListFlat[i]!=funcContextDict[fN][0]):
                    print("Debug Error, Func DataPos not match")
                funcContextDict[fN][1].append([funcName, upData.copy()])
def ArgTrace():
    global resRepGlobListFlat, PickList
    rrNum = len(resRepGlobListFlat)
    pNum = len(PickList)
    argNum = pNum - rrNum
    sRange = range(rrNum)
    ansPosLists = []
    for i in range(argNum):
        posList = MapFowardSearch([pNum - i - 1], sRange)
        ansPosLists.append(posList)
    return ansPosLists
def returnTrace():
    global resRepGlobListFlat
    rrNum = len(resRepGlobListFlat)
    returnList = []
    returnControlList = []
    sRange = range(rrNum)
    for i in range(rrNum):
        if (resRepGlobListFlat[i][0] == "Return"):
            if (resRepGlobListFlat[i][1] == []):
                continue
            ci = 0
            while(data2RR[ci]<=i):
                ci = ci + 1
            ci = ci - 1
            returnControlList.append(ci)
            returnList.append(resRepGlobListFlat[i][1][0])
    returnMarkList = [0 for _ in returnList]
    return returnList, returnControlList, returnMarkList
def sigFunExtend(funcPos):
    global resRepGlobListFlat, PickList
    pLen = len(PickList)
    rLen = len(resRepGlobListFlat)
    uprange = list(range(funcPos))
    uprange.extend(list(range(rLen, pLen)))
    uprrLs, dataLs = MapBackSearch([funcPos], uprange)
    return uprrLs, dataLs

def FindNameInVarList(targetName, varList):
    targetTokenList = targetName.token
    varNum = len(varList)
    tNum = len(targetTokenList)
    for i in range(varNum):
        sigVar = varList[i]
        if (sigVar.compelxGroup == None):
            if(targetTokenList[0] == sigVar.token):
                return [targetTokenList[0]]
        else:
            cNum = len(sigVar.compelxGroup)
            for sigC in range(cNum):
                sameFlag = True
                scNum = len(sigVar.compelxGroup[sigC])
                kNum = min(scNum, tNum)
                for j in range(kNum):
                    if (targetTokenList[j] != sigVar.compelxGroup[sigC][j]):
                        sameFlag = False
                        break
                if (sameFlag == True):
                    return sigVar.compelxGroup[sigC]
    return None
def VarListNormalize(varList):
    ansList = []
    counter = 0
    for eachVar in varList:
        ans = eachVar.norm
        counter = counter + 1
        if (ans == None):
            print("Doesn't find:", eachVar.ArgType, eachVar.itemList)
        ansList.append(ans)
    return ansList
def SigVarGetBased(var):
    if (var.compelxGroup == None):
        return var.token
    else:
        return complexGroup2BasedList(var.compelxGroup)
def complexGroup2BasedList(complexGroup):
    ans = []
    for sigG in complexGroup:
        ans.append(sigG[0])
    return ans
def VarListGetBasedList(varList):
    ans = []
    for sigVar in varList:
        ans.append(SigVarGetBased(sigVar))
    return ans
def InBasedList(basedList, targetList, easyMode = True):
    if (targetList == []):
        print("Error Empty Target, need to check!")
        return False
    if (easyMode):
        for sigBased in basedList:
            if (sigBased == []):

                continue
            if (targetList[0] == sigBased[0]):

                return True
        return False
    else:
        tNum = len(targetList)
        for sigBased in basedList:
            bNum = len(sigBased)
            num = min(bNum, tNum)
            findFlag = True
            for i in range(num):
                if (sigBased[i] != targetList[i]):
                    findFlag = False
                    break
            if findFlag == True:
                return True
        return False
def constrantListNormalize(constrantList, s, e, es, ee):
    ans = []
    for sigConst in constrantList:
        sigConst = ConsListOrderNomalize(sigConst)
        imptAns, imptBList = ConstrantNormalize(copy.deepcopy(sigConst))
        ans.append(["CHECK", [imptAns], [sigConst], s, e, es, ee, imptBList])
    return ans
def AssignMatch(sigConst, useBList):
    global AssignDict
    if (sigConst.ArgType == "Arg"):
        if (useBList):
            k = BList2String(sigConst.bList)
            if (k !="" and k in AssignDict):
                return AssignDict[k]
        else:
            if (len(sigConst.norm) == 1):
                k = " ".join(sigConst.norm[0])
                if (k in AssignDict):
                    return AssignDict[k]
    return None
def FuncMatch(sigConst):
    global AssignDict
    if (sigConst.ArgType == "FuncCall"):
        k = sigConst.name
        if (k in AssignDict):
            return AssignDict[k]
    return None
def ConstrainReplace(sigConst, AssignMatchFlag = True):
    global AssignDict
    if (sigConst[1] == "&&"):
        left = None
        if (isinstance(sigConst[0], list)):
            left = ConstrainReplace(sigConst[0])
        else:
            left = sigConst[0]
            if (AssignMatchFlag):
                tempt = AssignMatch(sigConst[0], True)
            else:
                tempt = FuncMatch(sigConst[0])
            if (tempt!=None):
                left = tempt
        right = None
        rightbList = []
        if (isinstance(sigConst[2], list)):

            right = ConstrainReplace(sigConst[2])
        else:
            right = sigConst[0]
            if (AssignMatchFlag):
                tempt = AssignMatch(sigConst[2], True)
            else:
                tempt = FuncMatch(sigConst[2])
            if (tempt!=None):
                right = tempt
        return [left, sigConst[1], right]
    elif (sigConst[1] in guardSigList[0]):
        left = sigConst[0]
        if (AssignMatchFlag):
            tempt = AssignMatch(sigConst[0], True)
        else:
            tempt = FuncMatch(sigConst[0])
        if (tempt!=None):
            left = tempt
        right = sigConst[2]
        if (AssignMatchFlag):
            tempt = AssignMatch(sigConst[2], True)
        else:
            tempt = FuncMatch(sigConst[2])
        if (tempt!=None):
            right = tempt
        return [left, sigConst[1], right]
    else:
        if (AssignMatchFlag):
            if (sigConst.ArgType == "Arg" and sigConst.norm!=[["__HardCodedVar__"]]):
                tempt = AssignMatch(sigConst, True)
                if (tempt != None):
                    return tempt
        else:
            if (sigConst.ArgType == "FuncCall"):
                tempt = FuncMatch(sigConst)
                if (tempt != None):
                    return tempt
        return sigConst
def ConstrantNormalize(sigConst, AssignReplace = False, useBList = False):
    global guardSigList, AssignDict
    if (sigConst[1] == "&&"):
        left = None
        leftbList = []
        if (isinstance(sigConst[0], list)):
            left, leftbList = ConstrantNormalize(sigConst[0], AssignReplace)
        else:
            left = sigConst[0].norm
            if (AssignReplace):
                tempt = AssignMatch(sigConst[0], useBList)
                if (tempt!=None):
                    left = tempt
            leftbList = sigConst[0].bList
        right = None
        rightbList = []
        if (isinstance(sigConst[2], list)):
            right, rightbList = ConstrantNormalize(sigConst[2], AssignReplace)
        else:
            right = sigConst[2].norm
            if (AssignReplace):
                tempt = AssignMatch(sigConst[2], useBList)
                if (tempt!=None):
                    right = tempt
            rightbList = sigConst[2].bList
        totalBList = leftbList
        totalBList.extend(rightbList)
        return [left, "&&", right], totalBList
    elif (sigConst[1] in guardSigList[0]):
        left = None
        leftbList = []
        if (isinstance(sigConst[0], list)):
            print("Debug Error: ConstrantNormalize guardSigList list is reached 0", sigConst)
            left, leftbList = ConstrantNormalize(sigConst[0][0], AssignReplace)
        else:
            left = sigConst[0].norm
            if (AssignReplace):
                tempt = AssignMatch(sigConst[0], useBList)
                if (tempt!=None):
                    left = tempt
            leftbList = sigConst[0].bList
        right = None
        rightbList = []
        if (isinstance(sigConst[2], list)):

            print("Debug Error: ConstrantNormalize guardSigList list is reached 2", sigConst)
            right, rightbList = ConstrantNormalize(sigConst[2][0], AssignReplace)
        else:
            right = sigConst[2].norm
            if (AssignReplace):
                tempt = AssignMatch(sigConst[2], useBList)
                if (tempt!=None):
                    right = tempt
            rightbList = sigConst[2].bList
        totalBList = leftbList
        if (rightbList != None):
            totalBList.extend(rightbList)
        return [left, "CMP", right], totalBList
    else:
        if (sigConst.ArgType == "Arg"):
            if (AssignReplace):
                tempt = AssignMatch(sigConst, useBList)
                if (tempt != None):

                    return tempt, sigConst.bList

            return sigConst.norm, sigConst.bList
        else:
            return sigConst.norm, [["_*_FUNCCALL_*_", sigConst]]
def MulResRepExtend(imptList, needExtendList):
    for sigItem in needExtendList:
        imptList.extend(sigItem)
def CodeRep2ResRep(funcName, curFuncArgList, funcExtendThreshold):
    global codes, codeRepList, data2RR
    global resRepGlobList
    global defedVarNameList, defedVarTypeList
    global funcTypeDict, funcCallNumDict
    global TotalContentReturn, codeLevel
    ErrorPosList = []
    errorLogArgListList = []
    ans = []
    num = len(codeRepList)
    data2RR = []
    jumpList = [None for _ in range(num)]
    for i in range(num):
        data2RR.append(len(ans))
        imptResRep = []
        if (codeRepList[i][0] == "declartion"):
            _, cVarList, cVarType, leftVarList, rightVarListList = codeRepList[i]
            cNum = len(cVarList)
            basedList = []
            for j in range(cNum):
                sbList = cVarList[j].bList
                basedList.extend(sbList)
                if (sbList[0] not in defedVarNameList):
                    defedVarNameList.append(sbList[0])
                    defedVarTypeList.append(cVarType)
            leftNum = len(leftVarList)
            for j in range(leftNum):
                varNorm = leftVarList[j].norm
                if (varNorm[0][0]!=cVarType):
                    print("This is Wrong!!!!! CodeRep2ResRep Assign")
                    print("cVarType", cVarType)
                    print("leftVarList[j].itemList", leftVarList[j].itemList)
                    print("leftVarList[j].norm", leftVarList[j].norm, cVarType)
                leftBased = leftVarList[j].bList
                rightNum = len(rightVarListList[j])
                if (rightNum == 1 and rightVarListList[j][0].ArgType == "FuncCall"):
                    adfN = rightVarListList[j][0].name
                    if (adfN not in funcTypeDict):
                        funcTypeDict[adfN] = cVarType
                affectRightList = []
                for k in range(rightNum):
                    sigRightNorm = rightVarListList[j][k].norm
                    if (sigRightNorm == None):
                        continue
                    affectRightList.append(sigRightNorm)
                    if (sigRightNorm == [["__HardCodedVar__"]]):
                        continue
                    if (rightVarListList[j][k].ArgType == "FuncCall"):
                        continue
                imptResRep.append(["Assign", varNorm, affectRightList, leftVarList[j], rightVarListList[j], leftBased])
                if (affectRightList == []):
                    print("Assign Error:Empty assign")
        elif (codeRepList[i][0] == "assignment"):
            _, leftVar, rightVarList = codeRepList[i]
            leftVarBased = leftVar.bList
            varNorm = leftVar.norm
            if (varNorm != None and varNorm != [["__HardCodedVar__"]]):
                rightNum = 0
                if (rightVarList != None):
                    rightNum = len(rightVarList)
                if (rightNum == 1 and rightVarList[0].ArgType == "FuncCall"):
                    adfN = rightVarList[0].name
                    if (adfN not in funcTypeDict):
                        funcTypeDict[adfN] = leftVar.norm[0][0]
                affectRightList = []
                for k in range(rightNum):
                    sigRightNorm = rightVarList[k].norm
                    if (sigRightNorm == None):
                        continue
                    affectRightList.append(sigRightNorm)
                    if (sigRightNorm == [["__HardCodedVar__"]]):
                        continue
                    if (rightVarList[k].ArgType == "FuncCall"):
                        continue
                    sigRBased = rightVarList[k].bList
                    imptResRep.append(["Read", sigRightNorm, None, rightVarList[k], None, sigRBased])
                imptResRep.append(["Assign", varNorm, affectRightList, leftVar, rightVarList, leftVarBased])
        elif (codeRepList[i][0] == "Subscript"):
            _, leftVar, rightVar = codeRepList[i]
            if (rightVar!=None and rightVar.norm != [['__HardCodedVar__']]):
                leftNorm = leftVar.norm
                rightNorm = rightVar.norm
                if (leftNorm != None and rightNorm != None and leftNorm != ["__HardCodedVar__"]):
                    imptBL = leftVar.bList
                    imptBL.extend(rightVar.bList)

                    imptResRep.append(["Read", rightNorm, None, leftVar, None, rightVar.bList])
                    imptResRep.append(["Read", leftNorm, rightNorm, leftVar, rightVar, imptBL])
            else:
                leftNorm = leftVar.norm
                if (leftNorm != None and leftNorm != ["__HardCodedVar__"]):
                    imptBL = leftVar.bList
                    imptResRep.append(["Read", leftNorm, None, leftVar, None, imptBL])
        elif (codeRepList[i][0] == "call_expression"):
            _, IsErrorLog, funcCall = codeRepList[i]
            if(funcCall.name in funcCallNumDict):
                funcCallNumDict[funcCall.name] += 1
            else:
                funcCallNumDict[funcCall.name] = 1
            if (IsErrorLog):
                ErrorPosList.append(i)
                errorLogArgListList.append(funcCall.argList)
            if (funcCall.argList == None):
                imptResRep.append(["FuncCall", funcCall, [[]]])
            else:
                aList = funcCall.argList
                aNum = len(funcCall.argList)
                funcBList = []
                for sigA in range(aNum):
                    if (aList[sigA] == None):
                        funcBList.append([])
                        continue
                    normedArg = aList[sigA].norm
                    ArgBList = aList[sigA].bList
                    if (normedArg == None):
                        funcBList.append([])
                        continue
                    if (normedArg == [["__HardCodedVar__"]]):
                        funcBList.append([])
                        continue
                    funcBList.append(ArgBList)
                imptResRep.append(["FuncCall", funcCall, funcBList])
        elif (codeRepList[i][0] == "if_statement"):
            _, elseExistFlag, s, gs, branchEndPos, se, elseEndPos, branchVarList, constrantList, bList = codeRepList[i]
            if (elseExistFlag):
                jumpList[i] = [se, elseEndPos]
                for clevel in range(gs+1, elseEndPos):
                    codeLevel[clevel] += 1
            else:
                for clevel in range(gs+1, branchEndPos):
                    codeLevel[clevel] += 1
            constrantList = constrantListNormalize(constrantList, s, branchEndPos, se, elseEndPos)
            imptResRep.extend(constrantList)
        elif (codeRepList[i][0] == "Assert"):
            _, constrantList, bList = codeRepList[i]
            for sigc in constrantList:
                sigc = ConsListOrderNomalize(sigc)
                imptAns, imptBList = ConstrantNormalize(copy.deepcopy(sigc))
                imptResRep.append(["CHECK", [imptAns], [sigc], imptBList])
        elif (codeRepList[i][0] == "switch_statement" or codeRepList[i] == "while_statement"):
            _, s, gs, branchEndPos, branchVarList, constrantList, bList = codeRepList[i]
            for clevel in range(gs+1, branchEndPos):
                codeLevel[clevel] += 1
            constrantList = constrantListNormalize(constrantList, s, branchEndPos, None, None)
            imptResRep.extend(constrantList)
        elif (codeRepList[i][0] == "return_statement"):
            _, aList = codeRepList[i]
            if (len(aList) == 1):
                if (aList[0].ArgType == "Arg"):
                    temptStr = BList2String(aList[0].bList)
                    if (temptStr in TotalContentReturn):
                        TotalContentReturn[temptStr] += 1
                    else:
                        TotalContentReturn[temptStr] = 1
            newbList = []
            for sigr in aList:
                newbList.extend(sigr.bList)
            imptResRep.append(["Return", aList, newbList])
        elif (codeRepList[i][0] == "else_statement"):
            imptResRep.append(["else_statement", [[]]])
        resRepGlobList.append(imptResRep)
        ActionList(imptResRep, ans)

    dataLen = len(ans)
    data2RR.append(dataLen)
    newjumpList = [None for _ in range(dataLen)]
    for i in range(num):
        if (jumpList[i] !=None):
            newi = data2RR[i+1]-1
            newjumpList[newi] = [None, None]
            newjumpList[newi][0] = data2RR[jumpList[i][0]]
            if (jumpList[i][1] == num):
                newjumpList[newi][1] = dataLen
            else:
                newjumpList[newi][1] = data2RR[jumpList[i][1]]
            if (newjumpList[newi][0]<=newi or newjumpList[newi][1]<=newi):
                print("Error: Wrong JumpList!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
                newjumpList[newi] = None

    return ErrorPosList, errorLogArgListList, ans, newjumpList

def SigVarRepTrace(sigTargetName):
    global structTypeName, funcDefSumDict
    global codes, codeRepList, resRepGlobList
    num = len(codeRepList)
    ansResRep = []
    rrPosSortedList = []
    ansCode = []
    ansCodeRep = []
    ansPos = []
    for i in range(num):
        rNum = len(resRepGlobList[i])
        offset = data2RR[i]
        for r in range(rNum):
            sigResRep = resRepGlobList[i][r]
            if (sigResRep == None or sigResRep == []):
                continue
            if (InBasedList(sigResRep[-1], sigTargetName) == True):
                ansResRep.append(sigResRep)
                rrPosSortedList.append(offset + r)
                if (i not in ansPos):
                    ansPos.append(i)
                    ansCode.append(codes[i])
                    ansCodeRep.append(codeRepList[i])
    rrPosSortedList, ansResRep = PosListSort(rrPosSortedList, ansResRep)
    return ansResRep, rrPosSortedList, ansCode, ansCodeRep
def findRelatedBranchPos(s, gs, bLists):
    global resRepGlobList, data2RR
    ans = []
    for sigb in bLists:
        sigAnsList = []
        for i in range(s, gs+1):
            rNum = len(resRepGlobList[i])
            offset = data2RR[i]
            for j in range(rNum):
                curPos = offset + j
                if (BListMatch(resRepGlobList[i][j][-1], sigb)):
                    sigAnsList.append(curPos)
        ans.append(sigAnsList)
    return ans
def FindCheckRelatedPos(gs):
    global resRepGlobListFlat, data2RR
    s = data2RR[gs+1]-1
    relatedPosList = []
    while(resRepGlobListFlat[s][0] == "CHECK"):
        relatedPosList.append([s])
        s = s -1
    relatedPosList = list(reversed(relatedPosList))
    return relatedPosList
FalseList = ["False", "FALSE", "false", "null", "0"]
TrueList = ["True", "TRUE"]
funcEHEXList = []
CurCHECKFuncEXList = []
CHECKFuncEXList = []
def rMatch(arg1, sourceName, fName, consPos):
    global zeroArg, CurCHECKFuncEXList, funcEHEXList
    if (fName not in funcDefSumDict):
        return
    returnList = funcDefSumDict[fName][4]
    findFlag = False
    rNum = len(returnList)
    if (arg1 == zeroArg or (arg1.norm == [['__HardCodedVar__']] and arg1.itemList[0][0] in FalseList)):
        for r in range(rNum):
            sigr = returnList[r]
            if (sigr.ArgType != "Arg"):
                continue
            if (sigr.norm == [['__HardCodedVar__']] and sigr.itemList[0][0] in FalseList):
                findFlag = True
                if (funcDefSumDict[fName][6][r] == 0):
                    funcDefSumDict[fName][6][r] = 1
                    if(fName not in funcEHEXList):
                        funcEHEXList.append(fName)
            if (sigr.ArgType == "FuncCall" and sigr.name!=fName):
                nf = rMatch(arg1, sourceName, sigr.name, consPos)
                if (nf):
                    CurCHECKFuncEXList.append([consPos, fName, r, sourceName])
                    findFlag = True
    return findFlag
def BackGroundSet(funcName):
    global funcBackGround, codes, codeRepList, resRepGlobList, resRepGlobListFlat, rrDataGlobListFlat, data2RR
    global resRepMapInfo, resRepRudu, PickList, BranchEHMark, EHBranch
    if (funcName in funcBackGround):
        codes, codeRepList, resRepGlobList, resRepGlobListFlat, rrDataGlobListFlat, data2RR,\
            resRepMapInfo, resRepRudu, PickList, BranchEHMark, EHBranch = funcBackGround[funcName]
        return True
    return False
def MoreEHFind():
    global funcEHEXList, funcDefSumDict, funcBackGround, CHECKFuncEXList
    for sigfunc in funcEHEXList:
        temptPosList = []
        rPosList, rMarkList = funcDefSumDict[sigfunc][5:7]
        argInfo = funcDefSumDict[sigfunc][1]
        rNum = len(rMarkList)
        for i in range(rNum):
            if (rMarkList[i] == 1):
                temptPosList.append(rPosList[i])
        BackGroundSet(sigfunc)
        imptC, _ = EHProcess(temptPosList, argInfo)
        imptC = meteralDivide(imptC, sigfunc+"MoreEHFind")
        funcDefSumDict[sigfunc][7].extend(imptC)
    for sigFName, returnPos, sigSouceName, constrain, unconstList, dRR, dData in CHECKFuncEXList:
        if (BackGroundSet(sigFName) == False):
            continue
        rPosList = funcDefSumDict[sigFName][5]
        argInfo = funcDefSumDict[sigFName][1]
        upperRange = list(range(0, rPosList))
        upperRange = upperRangeAdjust(upperRange, rPosList)
        rrN = len(resRepGlobListFlat)
        argN = len(PickList)
        upperRange.extend(list(range(rrN, rrN + argN)))
        backPosList = MapBackSearch([returnPos], upperRange)
        upRRLists, upDataLists = Pos2RRData(backPosList, True)
        constrain, unconstList = ConstrainReMake(constrain, unconstList, sigFName, sigSouceName)
        temp = ConstrantRelation(constrain, unconstList, upRRLists, upDataLists, dRR, dData)
        imptC = meteralDivide([temp], sigFName + "MoreEHFind Func")
        funcDefSumDict[sigFName][7].extend(imptC)
def ConstrainReMake(constrain, unconstList, sigFName, souceName):
    global AssignDict
    newFunc = FuncCallInfo(sigFName, None, None, None, None)
    AssignDict[souceName] = newFunc
    newUnConstList = ConstrainReplace(unconstList, False)
    newConstrain, _ = ConstrantNormalize(copy.deepcopy(newUnConstList))
    return newConstrain, newUnConstList
def ConstrainFuncExtend(gs, pos):
    global codeRepList, codes
    global funcDefSumDict
    rnum = len(resRepGlobList[gs])
    consTrainPos = 0
    drapFlagList = []
    for i in range(rnum):
        if (resRepGlobList[gs][i][0] == "CHECK"):
            constrantList = resRepGlobList[gs][i][2]
            cNum = len(constrantList)
            for sc in range(cNum):
                sigc = constrantList[sc]
                drapFlagList.append(False)

                if (len(sigc) == 3):
                    equalFlag = None
                    if (sigc[1] == "=="):
                        equalFlag = True
                    elif(sigc[1]=="!="):
                        equalFlag = False
                    else:
                        continue
                    f = None
                    arg = None
                    if(sigc[0].ArgType == "FuncCall" and sigc[2].ArgType == "Arg"):
                        f = sigc[0]
                        arg = sigc[2]
                    elif (sigc[2].ArgType == "FuncCall" and sigc[0].ArgType == "Arg"):
                        f = sigc[2]
                        arg = sigc[0]
                    else:
                        continue
                    if (f.name not in funcDefSumDict):
                        continue
                    findFlag = rMatch(arg, f.name, f.name, consTrainPos+sc)
                    if (findFlag):
                        drapFlagList[-1] = True
            consTrainPos = consTrainPos + cNum
    return drapFlagList
BranchEHMark = []
EHBranch = []
keywordList = ["err"]
def FindReturn(s, e):
    global codeRepList
    for i in range(s, e):
        if (codeRepList[i][0] == "return_statement"):
            if (codeRepList[i][1]!=None and len(codeRepList[i][1])==1):
                if (codeRepList[i][1][0].norm[0][0] == "__HardCodedVar__"):
                    return codeRepList[i][1][0].bList, i
                else:
                    for sigk in keywordList:
                        if(codeRepList[i][1][0].bList==[]):
                            continue
                        for sigb in codeRepList[i][1][0].bList[0]:
                            if sigk in sigb:
                                return codeRepList[i][1][0].bList, i
            return None, i
    return None, None

def ReturnLocat(sBList, sPosList):
    global codeRepList
    ansList = []
    crNum = len(codeRepList)
    for i in range(crNum):
        if (codeRepList[i][0] == "return_statement" and i not in sPosList):
            rarg = codeRepList[i][1]
            if (len(rarg)==1 and codeRepList[i][1][0]!=None):
                if (BListListMatch(codeRepList[i][1][0].bList, sBList)):
                    ansList.append(i)
    return ansList
def SigErrorGuardLocat(errorLogPos, threshold):
    global codes, codeRepList, resRepGlobList, BranchEHMark
    global EHBranch
    findRange = range(errorLogPos)
    findRange = list(reversed(findRange))
    counter = 0
    branchPosList = []
    brancVarList = []
    cList = []
    conList = []
    imptPosList = []
    drapFlagList = []
    sBList = []
    sPosList = []
    moreReturnPosList = []
    for i in findRange:
        if (codeRepList[i][0] == "if_statement"):
            _, elseExistFlag, s, gs, branchEndPos, se, elseEndPos, branchVarList, constrantList, bList = codeRepList[i]
            if (s<errorLogPos and errorLogPos<branchEndPos):
                if(gs in BranchEHMark):
                    break
                EHBranch.append([s, branchEndPos])
                rbList, rbPos = FindReturn(s, branchEndPos)
                sPosList.append(rbPos)
                if (rbList!=None):
                    sBList.append(rbList)
                BranchEHMark.append(gs)
                drapFlagList = ConstrainFuncExtend(gs, i)
                cLs, conLs, aL = GuardConsList(gs)
                imptPosList.append(aL)
                cList.append(cLs)
                conList.append(conLs)
                if (elseExistFlag):
                    branchPosList.append([s, gs, branchEndPos, elseEndPos, errorLogPos, False])
                else:
                    branchPosList.append([s, gs, branchEndPos, None, errorLogPos, False])
                brancVarList.append(branchVarList)
                counter = counter + 1
            elif (elseExistFlag and se<errorLogPos and errorLogPos<elseEndPos):
                if (gs in BranchEHMark):
                    break
                BranchEHMark.append(gs)
                EHBranch.append([se, elseEndPos])
                rbList, rbPos = FindReturn(se, elseEndPos)
                sPosList.append(rbPos)
                if (rbList != None):
                    sBList.append(rbList)
                drapFlagList = ConstrainFuncExtend(gs, i)
                cLs, conLs, aL = GuardConsList(gs)
                imptPosList.append(aL)
                cList.append(cLs)
                conList.append(conLs)
                branchPosList.append([s, gs, branchEndPos, elseEndPos, errorLogPos, True])
                brancVarList.append(branchVarList)
                counter = counter + 1
        elif (codeRepList[i][0] == "switch_statement" or codeRepList[i][0] == "while_statement" or codeRepList[i][0] == "do_statement"):
            _, s, gs, branchEndPos, branchVarList, constrantList, bList = codeRepList[i]
            if (gs in BranchEHMark):
                break
            EHBranch.append([s, branchEndPos])
            BranchEHMark.append(gs)
            rbList, rbPos = FindReturn(s, branchEndPos)
            if (rbPos!=None):
                sPosList.append(rbPos)
            if (rbList != None):
                sBList.append(rbList)
            drapFlagList = ConstrainFuncExtend(gs, i)
            cLs, conLs, aL = GuardConsList(gs)
            imptPosList.append(aL)
            cList.append(cLs)
            conList.append(conLs)
            branchPosList.append([s, gs, branchEndPos, None, errorLogPos, False])
            brancVarList.append(branchVarList)
            counter = counter + 1
        if (counter >= threshold):
            break
    moreRPosList = ReturnLocat(sBList, sPosList)
    return branchPosList, brancVarList, cList, conList, imptPosList, counter, drapFlagList, moreRPosList
def GuardConsList(gs):
    global resRepGlobListFlat, data2RR
    cLists = []
    conLists = []
    relatedPosList = []
    s = data2RR[gs]
    e = data2RR[gs+1]
    for i in range(s, e):
        if (resRepGlobListFlat[i][0] == "CHECK"):
            cLists.extend(resRepGlobListFlat[i][1])
            conLists.extend(resRepGlobListFlat[i][2])
            if (len(resRepGlobListFlat[i][1])>1):
                print("GuardConsList is the issue")
            relatedPosList.append([i])
    return cLists, conLists, relatedPosList
def showConstrain(constrain):
    ans = []
    for sigItem in constrain:
        if (isinstance(sigItem, list)):
            ans.append(showConstrain(sigItem))
        elif (isinstance(sigItem, str)):
            ans.append(sigItem)
        elif (sigItem.ArgType=="FuncCall"):
            ans.append(sigItem.name)
        else:
            ans.append(sigItem.itemStr)
    return " ".join(ans)
def showConstrainAndContext(findedConstrainAndContext):
    print("showConstrainAndContext")
    for sigCNC in findedConstrainAndContext:
        strCon = showConstrain(sigCNC.consList)
        print("constrain", strCon)
        print("up", sigCNC.forwardList)
        print("down", sigCNC.backwardList)

def EHProcess(errorLogList, argInfo):
    num = len(errorLogList)
    findedConstrainAndContext = []
    moreRPosList = []
    for sign in range(num):
        sigEH = errorLogList[sign]
        constrainInfo, mpList = EHTrace(sigEH, argInfo)
        moreRPosList.extend(mpList)
        findedConstrainAndContext.extend(constrainInfo)
    return findedConstrainAndContext, moreRPosList
def upperRangeAdjust(upperRange, errorGuardPos):
    global data2RR
    delList = []
    for i in upperRange:
        if (codeRepList[i][0] == "if_statement"):
            _, elseExistFlag, s, _, branchEndPos, se, elseEndPos, _, _, _ = codeRepList[i]
            if (elseExistFlag and se<=errorGuardPos and errorGuardPos<=elseEndPos):
                delList.append([s, branchEndPos])
    newUpperRange = []
    for i in upperRange:
        addFlag = True
        for eachDel in delList:
            if (eachDel[0] <= i and i <= eachDel[1]):
                addFlag = False
                break
        if (addFlag):
            newUpperRange.extend(list(range(data2RR[i], data2RR[i+1])))
    return newUpperRange
def EHTrace(errorLogPos, argInfo):
    global resRepGlobList, resRepGlobListFlat
    global codes
    global CHECKFuncEXList, CurCHECKFuncEXList
    totalNum = len(codes)
    rrFlatNum = len(resRepGlobListFlat)
    branchFindThreshold = 1
    relationThreshold = 4
    CurCHECKFuncEXList = []
    branchPosList, brancVarList, constrainList, unconstList, relatedPosList, counter, drapFlagList, moreRPosList = SigErrorGuardLocat(errorLogPos, branchFindThreshold)
    ans = []
    branchNum = len(branchPosList)
    argN = len(argInfo)
    rrN = len(resRepGlobListFlat)
    cNum = len(codes)
    for i in range(branchNum):
        sigBranchPos = branchPosList[i]
        upperRange = list(range(0, sigBranchPos[1]))
        upperRange = upperRangeAdjust(upperRange, sigBranchPos[1])
        upperRange.extend(list(range(rrN, rrN+argN)))
        lowerRange = []
        if (sigBranchPos[3]==None):
            lowerRange = list(range(data2RR[sigBranchPos[2]], rrFlatNum))
        elif(sigBranchPos[-1]==True):
            lowerRange = list(range(data2RR[sigBranchPos[0] + 1], data2RR[sigBranchPos[1]]))
            lowerRange.extend(list(range(data2RR[sigBranchPos[3]]+1, rrFlatNum)))
        else:

            lowerRange = list(range(data2RR[sigBranchPos[2] + 1], data2RR[sigBranchPos[3]]))
        cNum = len(constrainList[i])
        for jtk in range(cNum):
            if (drapFlagList[jtk] == True):
                continue
            upRRLists, upDataLists, downRRLists, downDataLists = BListSearch(upperRange, lowerRange, relatedPosList[i][jtk])
            if (upDataLists!=[] or downRRLists !=[]):
                for sigc in CurCHECKFuncEXList:
                    if (sigc[0] == jtk):
                        CHECKFuncEXList.append([sigc[1], sigc[2], sigc[3], constrainList[i][jtk], unconstList[i][jtk], downRRLists, downDataLists])
                temp = ConstrantRelation(constrainList[i][jtk], unconstList[i][jtk], upRRLists, upDataLists, downRRLists, downDataLists)
                ans.append(temp)
    return ans, moreRPosList
def sortFunc(a,b):
    if (a[0]<b[0]):
        return True
    elif (a[1]<b[1]):
        return True
    return False
def searchRangeCut(ans, searchRange):
    return list(set(ans).intersection(set(searchRange)))
def ansListSort(ansList):
    global resRepGlobListFlat, PickList
    nodeNum = len(resRepGlobListFlat)
    argNum = len(PickList)-nodeNum
    aL = []
    newAnsList= []
    for i in ansList:
        if i >= nodeNum:
            aL.append(argNum-(i-nodeNum)-1)
        else:
            newAnsList.append(i)
    newAnsList, rrL, dataL = PosSort(newAnsList)
    return newAnsList, rrL, dataL, aL
def PosSort(posList):
    global globalSortedList, resRepGlobListFlat, rrDataGlobListFlat
    newPosList = []
    rrL = []
    dataL = []
    for i in globalSortedList:
        if i in posList:
            newPosList.append(i)
            rrL.append(resRepGlobListFlat[i])
            dataL.append(rrDataGlobListFlat[i])
    return newPosList, rrL, dataL
def MapFowardSearch(posList, searchRange):
    global resRepMapInfo
    global resRepGlobList, PickList, resRepGlobListFlat
    rrNum = len(resRepGlobListFlat)
    pN = len(PickList)
    ans = []
    ans.extend(posList)
    newPosList = []
    for i in posList:
        for sigj in resRepMapInfo[i]:
            if (sigj not in ans):
                newPosList.append(sigj)
                ans.append(sigj)
    ans = searchRangeCut(ans, searchRange)
    ans = ForwardCut(ans)
    return ans
ForwardCutList = ["Return", "CHECK", "else_statement"]
def ForwardCut(ans):
    global resRepGlobListFlat
    newAns = []
    for i in ans:
        if (resRepGlobListFlat[i][0] in ForwardCutList):
            continue
        if (resRepGlobListFlat[i][0] == "FuncCall" and resRepGlobListFlat[i][1].isErrorLog == True):
            continue
        newAns.append(i)
    return newAns
def Pos2RRData(posList, extendFlag = False):
    _, rrL, dataL, aL = ansListSort(posList)
    if (aL != []):
        if (extendFlag):
            rrL.insert(0, ["Need Extend", aL])
            dataL.insert(0, None)
        else:
            print("Debug Error: Forward should Not have guest")
    return rrL, dataL
def MapBackSearch(posList, searchRange):
    global resRepGlobListFlat
    global resRepRudu
    global resRepGlobList
    rrNum = len(resRepGlobListFlat)
    pN = len(PickList)
    ans = []
    ans.extend(posList)
    while(posList!=[]):
        newPosList = []
        for i in posList:
            for sigj in resRepRudu[i]:
                if (sigj not in ans):
                    if(sigj >= rrNum or resRepGlobListFlat[sigj][0]!="FuncCall"):
                        newPosList.append(sigj)
                    ans.append(sigj)
        posList = newPosList
    ans = searchRangeCut(ans, searchRange)
    ans = BackCut(ans)
    return ans
BackCutList = ["Read", "CHECK", "else_statement", "Assign"]
def BackCut(ans):
    global resRepGlobListFlat, BackCutList
    newAns = []
    rrN = len(resRepGlobListFlat)
    for sigAns in ans:
        if (sigAns < rrN):
            if (resRepGlobListFlat[sigAns][0] in BackCutList):
                continue
            if (resRepGlobListFlat[sigAns][0] == "FuncCall" and resRepGlobListFlat[sigAns][1].isErrorLog == True):
                continue
        newAns.append(sigAns)
    return newAns
def ifElseProcess(ans):
    global ifElseList
    seta = set(ans)
    branchList = []
    for sigIfElse in ifElseList:
        s, gs, branchEndPos, se, elseEndPos = sigIfElse
        ifset = seta.intersection(set(range(gs+1, branchEndPos)))
        if (len(ifset) == 0):
            continue
        elseset = seta.intersection(set(range(se+1, elseEndPos)))
        if (len(elseset) == 0):
            continue
        branchList.append([ifset, elseset])
        seta = seta-ifset-elseset
    setList = [seta]
    for sigBranchList in branchList:
        setList = setCombine(setList, sigBranchList)
    ansList = sets2Lists(setList)
    return ansList
def setCombine(setsa, setsb):
    ansList = []
    for sa in setsa:
        for sb in setsb:
            ansList.append(sa.union(sb))
    return ansList
def sets2Lists(sets):
    ansList = []
    for s in sets:
        ansList.append(list(s))
    return ansList
def ListsConcat(listsa, listsb):
    if (listsa == []):
        return listsb
    aNum = len(listsa)
    bNum = len(listsb)
    ans = []
    for i in range(aNum):
        for j in range(bNum):
            ans.append(listsa[i]+listsb[j])
    return ans
def BListSearch(upSearchRange, downSearchRange, posList):
    global resRepGlobList
    global codes
    global codeRepList
    backPosList = MapBackSearch(posList, upSearchRange)
    upRRLists, upDataLists = Pos2RRData(backPosList, True)
    forwardPosList = MapFowardSearch(posList, downSearchRange)
    downRRLists, downDataLists = Pos2RRData(forwardPosList)
    return upRRLists, upDataLists, downRRLists, downDataLists
def ClassProcess(filePos, nodePos):
    global defedClassName, defedClassInfo
    classNamePos, endPos = TypeFindFirstInSubTree(nodePos, "identifier")
    defedClassName.append(tokenList[classNamePos])
    defedClassInfo.append((filePos, nodePos))
    return endPos
def TypeDefineProcess(filePos, nodePos):
    global defedAliasName, defedAliasInfo
    posList, ePos = TypeFindInSubTree(nodePos, "type_identifier")
    if (posList!=None):
        directChildList = DirectChildrenList(nodePos)
        pos = TypeFindInList(directChildList, "struct_specifier")
        if (pos!=-1):
            defedStructName.append(tokenList[posList[-1]])
            defedStructInfo.append((filePos, nodePos, tokenList[nodePos]))
        defedAliasName.append(tokenList[posList[-1]])
        defedAliasInfo.append((filePos, nodePos))
    return ePos
def StructProcess(filePos, nodePos):
    global defedStructName, defedStructInfo
    namePos, ePos = TypeFindFirstInSubTree(nodePos, "type_identifier")
    if (namePos!=None):
        defedStructName.append(tokenList[namePos])
        defedStructInfo.append((filePos, nodePos, tokenList[nodePos]))
    return ePos
def UnionProcess(filePos, nodePos):
    global defedStructName, defedStructInfo
    namePos, ePos = TypeFindFirstInSubTree(nodePos, "type_identifier")
    if (namePos != None):
        defedStructName.append(tokenList[namePos])
        defedStructInfo.append((filePos, nodePos, tokenList[nodePos]))
    return ePos
def IsNumber(a):
    for i in a:
        if i < '0' or i > '9':
            return False
    return True
def PreDefineProcess(filePos, nodePos):
    global GlobalResNameList, GlobalResTypeList
    namePos, ePos = TypeFindFirstInSubTree(nodePos, "identifier")
    replacWithPos, _ = TypeFindFirstInSubTree(nodePos, "preproc_arg")
    if (namePos != None and replacWithPos!= None and IsNumber(tokenList[replacWithPos])):
        if (tokenList[namePos] not in GlobalResNameList):
            GlobalResNameList.append(tokenList[namePos])
            GlobalResTypeList.append("__HardCodedVar__")
        else:
            print("Warnning: Repeat Var")
            GlobalResTypeList[GlobalResNameList.index(tokenList[namePos])] = "__HardCodedVar__"
    return ePos
def sigCharJudge(sigChar):
    if (sigChar>='a' and sigChar<='z' or sigChar>='A' and sigChar<='Z' or sigChar>='0' and sigChar<='9' or sigChar == '_'):
        return True
    return False
def ReplaceListFormat(argFormNameList, replacedWith):
    strLen = len(replacedWith)
    replaceList = []
    repOrder = []
    if (argFormNameList == []):
        return replaceList, repOrder
    lastStart = 0
    start = 0
    end = 1
    num = len(replacedWith)
    while (start<num and not sigCharJudge(replacedWith[start])):
        start = end
        end = end + 1
    while (end<strLen):
        if not sigCharJudge(replacedWith[end]):
            identifierName = replacedWith[start:end]
            if (identifierName in argFormNameList):
                replaceList.append(replacedWith[lastStart:start].strip())
                repPos = argFormNameList.index(identifierName)
                repOrder.append(repPos)
                lastStart = end
            start = end
            end = end + 1
            while (start<strLen and not sigCharJudge(replacedWith[start])):
                start = end
                end = end + 1
        else:
            end = end + 1
    replaceList.append(replacedWith[lastStart:].strip())
    return replaceList, repOrder
def PreDefineFuncProcess(filePos, nodePos):
    global preDefineFuncName, preDefineFuncInfo
    namePos, ePos = TypeFindFirstInSubTree(nodePos, "identifier")
    argFormNameListPos, _ = TypeFindFirstInSubTree(nodePos, "preproc_params")
    if (namePos != None and argFormNameListPos != None):
        idPosList, _ = TypeFindInSubTree(argFormNameListPos, "identifier")
        replacedWithPos, _ = TypeFindFirstInSubTree(nodePos, "preproc_arg")
        if (replacedWithPos!=None):
            aliasForm = tokenList[namePos] + tokenList[argFormNameListPos]
            argFormNameList = PosList2NameList(idPosList)
            replacedWith = tokenList[replacedWithPos]
            aliasReplaceList, _ = ReplaceListFormat(argFormNameList, aliasForm)
            replaceList, repOrder = ReplaceListFormat(argFormNameList, replacedWith)
            preDefineFuncName.append(tokenList[namePos])
            preDefineFuncInfo.append((filePos, nodePos, argFormNameList, aliasReplaceList, replaceList, repOrder))
        else:
            print("Debug Error: idPosList not equal to replacedWithPos", tokenList[nodePos])
    else:
        print("Debug Error: PreDefineFuncProcess skipped", tokenList[nodePos])
    return ePos
def FuncDefCallGraphProcess(nodePos):
    tPos, ePos = TypesFindFirstInSubTree(nodePos, ["primitive_type", "type_identifier", "sized_type_specifier"])
    if (tPos == None):
        return None
    funcType = tokenList[tPos]
    decPos, _ = TypeFindFirstInSubTree(nodePos, "function_declarator")
    if (decPos == None or tPos > decPos):
        return None
    funcNamePos, rPos = TypeFindFirstInSubTree(decPos, "identifier")
    if (funcNamePos == None):
        return None
    funcName = tokenList[funcNamePos]
    funcCallNameList = []
    funcCallList, assignEndPos = TypeFindInSubTree(nodePos, "call_expression")
    for sigFunc in funcCallList:
        funcCallNameList.append(tokenList[sigFunc + 1])
    funcCallNameList = list(set(funcCallNameList))
    return funcType, funcName, funcCallNameList
def CallGraph(filePos):
    NameList = []
    PosList = []
    TypeList = []
    Adj = {}
    num = len(typeList)
    i = 0
    while (i<num):

        if typeList[i] == "function_definition":
            classFilterPos, iRangeE = TypeFindFirstInSubTree(i, "type_identifier")
            if (classFilterPos == None or tokenList[classFilterPos] != "class"):
                impt = FuncDefCallGraphProcess(i)
                if (impt != None):
                    funcType, funcName, funcCallNameList = impt
                    if (funcName in NameList):
                        i = iRangeE + 1
                        continue
                    TypeList.append(funcType)
                    NameList.append(funcName)
                    PosList.append((filePos, i))
                    Adj[funcName] = funcCallNameList

                i = iRangeE + 1
            elif (tokenList[classFilterPos] == "class"):
                ePos = ClassProcess(filePos, i)
                i = ePos + 1
            else:
                i = i + 1
        elif (typeList[i] == "preproc_def"):
            ePos = PreDefineProcess(filePos, i)
            i = ePos + 1
        elif (typeList[i] == "type_definition"):
            ePos = TypeDefineProcess(filePos, i)
            i = ePos + 1
        elif (typeList[i] == "struct_specifier"):

            ePos = StructProcess(filePos, i)
            i = ePos + 1
        elif (typeList[i] == "union_specifier"):
            ePos = UnionProcess(filePos, i)
            i = ePos + 1
        elif (typeList[i] == "declaration"):
            createdVar, createdVarType, ePos = GlobalDeclarProcess(i)
            i = ePos + 1
        elif (typeList[i] == "field_declaration"):
            ePos = RangeEndPosFind(i)
            print("Warnning: UnPorcessed:", tokenList[relation[i]])
            i = ePos + 1
        else:
            i = i + 1
    return NameList, PosList, TypeList, Adj
def GloabDefCapture(filePos):
    num = len(typeList)
    i = 0
    while (i<num):
        if (typeList[i] == "preproc_def"):
            ePos = PreDefineProcess(filePos, i)
            i = ePos + 1
        else:
            i = i + 1
stateIDList = {}
def GotoHandle():
    global codes, codeRepList, stateIDList
    stateIDList = {}
    stateCount()
    codeNum = len(codes)
    nC, nCRL = GotoRepFormNewCodeRep(0, codeNum, -1, 0)
    codes = nC
    codeRepList = nCRL
def stateCount():
    global codes, codeRepList, stateIDList
    stateIDList = {}
    codeNum = len(codes)
    for stateS in range(codeNum):
        if (codeRepList[stateS][0] == "statementID"):
            for stateE in range(stateS + 1, codeNum):
                if (codeRepList[stateE][0] == "return_statement" or stateE == codeNum - 1):
                    imptList = codes[stateS+1:stateE+1].copy()
                    imptList[0] = "---------GOTO----------\n" + imptList[0]
                    imptList[-1] = imptList[-1] + "\n---------GOTO END----------\n"
                    stateIDList[codeRepList[stateS][1]] = [stateS+1, imptList, codeRepList[stateS+1:stateE+1].copy()]
def GotoRepFormNewCodeRep(start, end, branchPos, curnewCodeNum):

    global codes, codeRepList, stateIDList

    if (start>end):
        print("Debug Info Wrong case:", codes[start-1])
    newCodes = []
    newCodeRepList = []
    lastPos = start
    i = start
    while(i<end):
        if (i == branchPos):
            i = i + 1
            continue
        if (codeRepList[i] == [] or codeRepList[i] == None):
            i = i + 1
            continue
        if (codeRepList[i][0] == "if_statement"):
            _, elseExistFlag, s, gs, branchEndPos, se, elseEndPos, bVarList, constrantList, bList = codeRepList[i]
            newCodes.extend(codes[lastPos:s])
            ns = len(newCodes) + curnewCodeNum
            newCodes.extend(codes[s:i])
            ngs = len(newCodes) + curnewCodeNum
            newCodes.append(codes[i])
            nc, ncr = GotoRepFormNewCodeRep(i+1, branchEndPos, i, len(newCodes) + curnewCodeNum)
            newCodes.extend(nc)
            nbranchEndPos = len(newCodes) + curnewCodeNum
            newIfCodeRep = codeRepList[i]
            newIfCodeRep[2] = ns
            newIfCodeRep[3] = ngs
            newIfCodeRep[4] = nbranchEndPos
            elncr = []
            if (elseExistFlag):
                newCodes.append(codes[se])
                elnc, elncr = GotoRepFormNewCodeRep(se+1, elseEndPos, i, len(newCodes) + curnewCodeNum)
                newCodes.extend(elnc)
                nelseEndPos = len(newCodes) + curnewCodeNum
                nse = nbranchEndPos
                newIfCodeRep[5] = nse
                newIfCodeRep[6] = nelseEndPos
            newCodeRepList.extend(codeRepList[lastPos:i])
            newCodeRepList.append(newIfCodeRep)
            newCodeRepList.extend(ncr)
            if (elseExistFlag):
                newCodeRepList.append(codeRepList[se])
                newCodeRepList.extend(elncr)
                i = elseEndPos
                lastPos = elseEndPos
            else:
                i = branchEndPos
                lastPos = branchEndPos
            if (len(newCodes)!= len(newCodeRepList)):
                print("Error Debug Length if", len(newCodes), len(newCodeRepList))
        elif (codeRepList[i][0] == "switch_statement" or codeRepList[i][0] == "while_statement" or codeRepList[i][0] == "do_statement"):
            _, s, gs, branchEndPos, branchVarList, branchRFlag, branchCCodes = codeRepList[i]
            newCodes.extend(codes[lastPos:s])
            ns = len(newCodes) + curnewCodeNum
            newCodes.extend(codes[s:i])
            ngs = len(newCodes) + curnewCodeNum
            newCodes.append(codes[i])
            nc, ncr = GotoRepFormNewCodeRep(i+1, branchEndPos, i, len(newCodes) + curnewCodeNum)
            newCodes.extend(nc)
            nbranchEndPos = len(newCodes) + curnewCodeNum
            newIfCodeRep = codeRepList[i]
            newIfCodeRep[2] = ns
            newIfCodeRep[3] = ngs
            newIfCodeRep[4] = nbranchEndPos
            newCodeRepList.extend(codeRepList[lastPos:i])
            newCodeRepList.append(newIfCodeRep)
            newCodeRepList.extend(ncr)
            lastPos = branchEndPos
            i = branchEndPos
            curcodeLen = len(newCodes)
            if (len(newCodes) != len(newCodeRepList)):
                print("Debug Error Length switch", len(newCodes), len(newCodeRepList))
        elif (codeRepList[i][0] == "goto_statement"):
            newCodes.extend(codes[lastPos:i])
            newCodeRepList.extend(codeRepList[lastPos:i])
            lastPos = i + 1
            _, gotoID = codeRepList[i]
            keyList = stateIDList.keys()
            if gotoID in keyList:
                biasStartPos, nCList, nCRList = stateIDList[gotoID]
                if (i<biasStartPos):
                    bias = len(newCodes) + curnewCodeNum - biasStartPos

                    newCodes.extend(nCList)
                    newCodeRepList.extend(branchCodeRepAdjust(bias, nCRList))
            else:
                print("This goto not found or cannot process!!!!!!!!!!!!!")
            if (len(newCodes) != len(newCodeRepList)):
                print("Debug Length Goto", len(newCodes), len(newCodeRepList))
            i = i + 1
        else:
            i = i + 1
    newCodes.extend(codes[lastPos:end])
    newCodeRepList.extend(codeRepList[lastPos:end])
    return newCodes, newCodeRepList
def branchCodeRepAdjust(bias, crpList):
    crList = copy.deepcopy(crpList)
    num = len(crList)
    for i in range(num):
        if (crList[i][0] == "if_statement"):
            crList[i][2] = crpList[i][2] + bias
            crList[i][3] = crpList[i][3] + bias
            crList[i][4] = crpList[i][4] + bias
            if (crList[i][1]):
                crList[i][5] = crpList[i][5] + bias
                crList[i][6] = crpList[i][6] + bias
        elif (crList[i][0] == "switch_statement" or crList[i][0] == "while_statement" or crList[i][0] == "do_statement"):
            crList[i][1] = crpList[i][1] + bias
            crList[i][2] = crpList[i][2] + bias
            crList[i][3] = crpList[i][3] + bias

    return crList
def FlatListSort(jumpList):
    global globalSortedList, resRepGlobListFlat, rrDataGlobListFlat
    num = len(globalSortedList)
    newJumpList = []
    ansrr = []
    ansData = []
    rrN = len(resRepGlobListFlat)
    for i in range(num):
        if (globalSortedList[i]>=rrN):
            continue
        ansrr.append(resRepGlobListFlat[globalSortedList[i]])
        ansData.append(rrDataGlobListFlat[globalSortedList[i]])
        newJumpList.append(jumpList[globalSortedList[i]])
    return ansrr, ansData, newJumpList
def FunDetailAnalysis(orderList):
    global tokenList, typeList, relation, relationLen
    global funcDefInfoDict, nameListForReach, fileTreeList
    global funcDefSumDict
    global codes, codeRepList
    global resRepGlobList
    global dataList
    numOrdList = len(orderList)
    for sP in range(numOrdList):
        i = orderList[sP]
        funcName = nameListForReach[i]
        print("\rFunDetailAnalysis:", sP, "/", numOrdList, funcName, end="        ", flush=True)
        pos, funcType, callList = funcDefInfoDict[funcName]
        tokenList = fileTreeList[pos[0]][0]
        typeList = fileTreeList[pos[0]][1]
        relation = fileTreeList[pos[0]][2]
        relationLen = len(relation)
        imptArg = FuncDetailInfoTrace(pos[0], pos[1], funcName, funcType)
        if (imptArg == None):
            continue

sigRoundReachList = []
fatherList = []
def reachAble(funcName):
    global funcDefInfoDict, skipList, treeReachedList, nameListForReach
    global fatherList
    pos = nameListForReach.index(funcName)
    treeReachedList[pos] = 1
    if (pos in fatherList):
        cutPos = fatherList.index(pos)
        fatherList = fatherList[:cutPos]
        skipList.append(funcName)
        return
    fatherList.append(pos)
    searchRange = funcDefInfoDict[funcName][2]
    for sigTargetFunc in searchRange:
        if(sigTargetFunc not in nameListForReach):
            continue
        if (sigTargetFunc in skipList):
            continue
        nPos = nameListForReach.index(sigTargetFunc)
        if (treeReachedList[nPos] == 1):
            continue
        reachAble(sigTargetFunc)
def FuncCallGraphAnalysis():
    global funcDefInfoDict
    global CallerDict, CallDict, skipList, nameListForReach
    global CerList, CList
    global treeReachedList, sigRoundReachList
    global fatherList
    CallerDict = {}
    CallDict = {}
    CerList = []
    CList = []
    skipList = []
    treeReachedList = []
    nameListForReach = list(funcDefInfoDict.keys())
    num = len(nameListForReach)
    for i in range(num):
        treeReachedList.append(0)
        funcName = nameListForReach[i]
        callList = funcDefInfoDict[funcName][2]
        if (funcName in callList):
            skipList.append(1)
        else:
            skipList.append(0)
    skipedNum = 0
    for ski in range(len(skipList)):
        if (skipList[ski] == 1):
            skipedNum = skipedNum + 1
    inList = []
    outList = []
    markList = []
    for i in range(num):
        if (skipList[i]==1):
            markList.append(1)
            outList.append(-1)
            inList.append(-1)
            continue
        markList.append(0)
        funcName = nameListForReach[i]
        callList = funcDefInfoDict[funcName][2]
        outList.append(0)
        inList.append(0)
        CallDict[funcName] = []
        CList.append(funcName)
        for sigFuncCall in callList:
            if (sigFuncCall not in nameListForReach or skipList[nameListForReach.index(sigFuncCall)] == 1):
                continue
            outList[-1] = outList[-1] + 1
            CallDict[funcName].append(sigFuncCall)
            if (sigFuncCall not in CerList):
                CallerDict[sigFuncCall] = [funcName]
                CerList.append(sigFuncCall)
                inList.append(1)
            else:
                CallerDict[sigFuncCall].append(funcName)
                ps = CerList.index(sigFuncCall)
                inList[ps] = inList[ps] + 1
    skipedNum = 0
    for ski in range(len(skipList)):
        if (skipList[ski] == 1):
            skipedNum = skipedNum + 1
    startList = []
    for i in range(num):
        if (inList[i] == 0):
            startList.append(i)
    groupedList = []
    zeroList = [0 for _ in range(num)]
    for i in startList:

        if (treeReachedList[i] == 0):
            sigRoundReachList = zeroList.copy()
            fatherList = []
            reachAble(nameListForReach[i])
            if (fatherList == []):
                continue
            groupedList.append(fatherList)
    cuttedNum = 0
    for i in skipList:
        cuttedNum = cuttedNum + i
    print("cuttedNum", cuttedNum, " out of ", len(nameListForReach))
    flag = 1
    ans = []
    while flag == 1:
        flag = 0
        for i in range(num):
            if (markList[i]==0 and skipList[i]!=1 and outList[i] == 0):
                ans.append(i)
                markList[i] = 1
                flag = 1
                if (nameListForReach[i] not in CallerDict.keys()):
                    continue
                callerList = CallerDict[nameListForReach[i]]
                for sigF in callerList:
                    pos = nameListForReach.index(sigF)
                    outList[pos] = outList[pos] - 1
    print("got: ", len(ans), "out of", num)
    counter = 0
    if (0 in markList):

        for i in range(num):
            if (markList[i] == 0):
                counter = counter + 1
                skipList[i] = 1
    return ans, skipList, nameListForReach, groupedList
codes = []
codeRepList = []
def ArgExtract(patternList, targetString):
    num = len(patternList)
    ansList = []
    if (len(patternList)==0):
        return ansList
    s = len(patternList[0])
    for i in range(1,num):
        e = targetString.find(patternList[i], s+1)
        if (e == -1):
            return None
        ansList.append(targetString[s:e].strip())
        s = e + len(patternList[i])
    return ansList
def ArgJoin(patternList, repOrder, argList):
    anslist = []
    num = len(repOrder)
    if (len(patternList)!=num+1):
        print("Debug Error:patternList is not equal to argList + 1")
        return None
    for i in range(num):
        anslist.append(patternList[i])
        anslist.append(argList[repOrder[i]])
    anslist.append(patternList[-1])
    ans = "".join(anslist)
    return ans
def PrintStructInfo(basicPath, proName, StructCode):
    basicPath = os.getcwd() + "/" + basicPath
    structInfoProPath = basicPath + proName + "/"
    if not os.path.exists(structInfoProPath):
        os.makedirs(structInfoProPath)
    num = len(StructCode)
    printedCounter = 0
    for i in range(num):
        imptContent = []
        print("\rWriting:", i, "out of", num, len(imptContent), end="        ", flush=True)
        sigStructTypeInfo = StructCode[i]
        structType, structCode, sigStructFunc = sigStructTypeInfo
        structTypePath = basicPath + proName + "/" + structType + ".txt"
        imptContent.append("******************************************")
        imptContent.append(structType)
        sigInfoNumTotal = 0
        sigInfoNumFull = 0
        sigInfoContainErrorLogNum = 0
        imptContent.append("******************************************\n")
        imptContent.append(structCode)
        imptContent.append("\n")
        imptContent.append("****************************************** ******************************************\n")
        for sigContent in sigStructFunc:
            sigFuncName, argNameList, argFindNameList, whereFindList, ansCodeListList = sigContent
            sigInfoNumTotal = sigInfoNumTotal + len(argNameList)
            imptContent.append("***********************")
            imptContent.append(sigFuncName)
            imptContent.append("***********************\n")
            argNum = len(argNameList)
            for imptI in range(argNum):
                imptContent.append("-----------------------------------------------------------------------")
                imptContent.append("argName: "+argNameList[imptI]+"\n")
                if (len(argFindNameList[imptI]) == 0 or len(ansCodeListList[imptI]) == 0):
                    imptContent.append("This Type is not complete!\n")
                    continue
                sigInfoNumFull = sigInfoNumFull + 1
                fNList = argFindNameList[imptI]
                whileF = whereFindList[imptI]
                imptContent.append("findNameList: ")
                imNum = len(fNList)
                for imi in range(imNum):
                    sigFN = fNList[imi]
                    sigWhere = whileF[imi]
                    imptContent.append(sigFN + " BASED ON " + sigWhere + "\n")
                imptContent.append("\n")
                imptContent.append("relatedCode:\n")
                ansCList = ansCodeListList[imptI]
                containErrorLog = False
                for sigCode in ansCList:
                    if ("__**Error Log**__" in sigCode):
                        containErrorLog  =True
                    imptContent.append(sigCode)
                    imptContent.append("\n")
                if (containErrorLog):
                    sigInfoContainErrorLogNum = sigInfoContainErrorLogNum + 1
        imptContent.append("**************************************************************************")
        imptContent.append("There are:" + str(sigInfoNumFull) + " out of " + str(sigInfoNumTotal) + " are complete lifecycle")
        imptContent.append("**************************************************************************\n")
        imptContent.append("**************************************************************************")
        imptContent.append("There are:" + str(sigInfoContainErrorLogNum) + " out of " + str(sigInfoNumFull) + " have been Error Handled")
        imptContent.append("**************************************************************************\n")
        if (sigInfoContainErrorLogNum>3):
            file = open(structTypePath, 'w', encoding='UTF-8')
            file.write(" ".join(imptContent))
            file.close()
            printedCounter = printedCounter + 1
    print("Write", printedCounter, "out of ", num)
def CommentRemove(code):
    lastPos = 0
    start = 0
    i = 1
    codeNum = len(code)
    ansList = []
    haveComment = False
    while(i<codeNum):
        if (code[i-1] == "/" and code[i] == "*"):
            start = i - 1
            haveComment = True
        elif (code[i-1] == "*" and code[i] == "/"):
            if (haveComment):
                ansList.append(code[lastPos:start])
                lastPos = i+1
                haveComment = False
            else:
                print("This comment end mark came out from no where!")
        i = i + 1
    ansList.append(code[lastPos:])
    code = "".join(ansList)
    codes = code.split("\n")
    newCodes = []
    for sigLineCode in codes:
        pos = sigLineCode.find("//")
        if (pos!=-1):
            newCodes.append(sigLineCode[:pos])
        else:
            newCodes.append(sigLineCode)
    code = "\n".join(newCodes)
    return code
def EqualConstrain(stuA, stuB):
    ac = stuA.showConstrain
    bc = stuB.showConstrain
    if (ac == bc):
        return True
    return False
def psSort(a,b):
    la = len(a[1])
    lb = len(b[1])
    if (la==lb and a[0] == b[0]):
        return 0
    elif (la==lb):
        return a[0]<b[0]
    else:
        return la<lb
def FindBestPat(ansList, guardP):
    bestcur = -1
    bestLen = -1
    result = None
    for siga in ansList:
        lsa = len(siga[1])
        if (lsa>bestLen):
            if (guardP in siga[1]):
                result = siga
                bestLen = lsa
                bestcur = siga[0]
        elif (lsa == bestLen and siga[0]>bestcur):
            if (guardP in siga[1]):
                result = siga
                bestLen = lsa
                bestcur = siga[0]
    return result
def MapMatch(data, guardP):
    num = len(data)
    ps = PrefixSpan(data)
    ans = ps.frequent(num*0.7, closed=True)
    if (len(ans) == 0):
        return None
    else:
        r = FindBestPat(ans, guardP)
        if (r == None):
            return None
        return r[1]

def PatternMine(data, guardP):
    ans = MapMatch(data, guardP)
    return ans
def RuleSelection(forwardActionList, backwardActionList, ansConstrain, checkPointList):
    print("To be continue")
    return forwardActionList[0], backwardActionList[0], ansConstrain[0]
def GroupStudy(data, guardP):
    if (len(data)==1):
        return data[0]
    else:
        return PatternMine(data, guardP)
def ShowStudyMeteral():
    global studyMeteral
    sNum = len(studyMeteral)
    print("ShowStudyMeteral Num", sNum)
    for s in range(sNum):
        print("s studyMeteral[s].indexList", studyMeteral[s].indexList)
        print("ShowStudyMeteral s", showContext(studyMeteral[s].indexList))
        print("show studymeteral cons", studyMeteral[s].showConstrain)
def MeteTrain():
    global studyMeteral
    global studyMeteralSource
    global globalContext
    global MeteTrainMinGroupNum, VarTrainMinGroupNum
    num = len(studyMeteral)
    marker = []
    patternList = []
    posList = []
    constrainList = []
    supportNum = []
    DebugDataList = []
    for i in range(num):
        marker.append(0)
    TotalNum = 0
    wantedNum = 0
    originNum = 0
    for i in range(num - 1):
        TotalNum += 1
        p = -1
        if (studyMeteral[i].showConstrain in globalContext):
            p = globalContext.index(studyMeteral[i].showConstrain)
        else:
            print("Debug Error!!!!!Constrain not saved!!!!")
            continue
        if p in studyMeteral[i].indexList:
            fP = studyMeteral[i].indexList.index(p)

            if (fP == 0):
                wantedNum += 1
            else:
                wflag = True
                for tk in range(fP):
                    sigStr = globalContext[studyMeteral[i].indexList[tk]]

                    fl = len("FuncCall")
                    if (len(sigStr)>fl and sigStr[:fl] == "FuncCall"):
                        wflag = False
                        fn = sigStr[fl + 1:]

                        if (fn in funcDefInfoDict):
                            originNum +=1
                            break
                if ("**_FUNC_CALL_**" in studyMeteral[i].showConstrain):
                    tempcList = studyMeteral[i].showConstrain.split(" ")
                    for sigt in tempcList:
                        if (funcCallMark in sigt):

                            if (sigt[len(funcCallMark):] in funcDefInfoDict):
                                originNum += 1
                    wflag = False
                if (wflag):
                    wantedNum += 1
    print("Static Result:", wantedNum, TotalNum, originNum)
    wantedPattern = 0
    totalPattern = 0
    for i in range(num):
        if (marker[i] == 1):
            continue
        groupList = [studyMeteral[i]]
        groupListSources = [studyMeteralSource[i]]
        constrain = studyMeteral[i].constrainIndex
        p = -1
        if (studyMeteral[i].showConstrain in globalContext):
            p = globalContext.index(studyMeteral[i].showConstrain)
        else:
            print("Debug Error!!!!!Constrain not saved!!!!")
            continue
        for j in range(i+1, num):
            if (marker[j] == 1):
                continue
            if (EqualConstrain(studyMeteral[i], studyMeteral[j])):
                marker[j] = 1
                groupList.append(studyMeteral[j])
                groupListSources.append(studyMeteralSource[j])
        if (len(set(groupListSources))<1):
            continue
        data = TrainProcess(groupList, groupListSources)
        if (len(data) == 0):
            continue
        contextList = GroupStudy(data, p)
        if (contextList==None or p not in contextList):
            print("Debug Error, This is not possible")
            continue
        tpos = contextList.index(p)
        constrainList.append(contextList[tpos])
        del contextList[tpos]
        if (contextList != [] and contextList != None and len(contextList)<=4):
            totalPattern+=1
            wflag = True
            for wpi in range(tpos):
                sigS = globalContext[contextList[wpi]]
                fl = len("FuncCall")
                if (len(sigS) > fl and sigS[:fl] == "FuncCall"):
                    wflag = False
            if (wflag):
                gSet = set(groupListSources)
                if (len(gSet)<VarTrainMinGroupNum):
                    del constrainList[-1]
                    continue
                wantedPattern += 1
            else:
                gSet = set(groupListSources)
                if (len(gSet)<MeteTrainMinGroupNum):
                    del constrainList[-1]
                    continue
            if (OnlyReadFlag):
                orFlag = False
                cLen = len(contextList)
                for sc in range(cLen):
                    sigS = globalContext[contextList[sc]]
                    fl = len("FuncCall")
                    if (len(sigS) > fl and sigS[:fl] == "FuncCall"):
                        orFlag = True
                        break
                if (not orFlag):
                    del constrainList[-1]
                    continue
            patternList.append([contextList, constrain])
            posList.append(tpos)
            supportNum.append(len(data))
            DebugDataList.append([data, groupListSources])
        else:
            del constrainList[-1]
    print(len(studyMeteral), " group into ", len(patternList), " pattern")
    return patternList, posList, constrainList, supportNum, DebugDataList
globalContext = []
def MulList2str(sigAction):
    ans = []
    for sigItem in sigAction:
        if (isinstance(sigItem, list)):
            ans.append(MulList2str(sigItem))
        elif (sigItem == None):
            continue
        else:
            ans.append(str(sigItem))
    return " ".join(ans)
def addGlobalContext(ans, tempt, sigAction):
    global globalContext
    if (tempt not in globalContext):
        ans.append(len(globalContext))
        globalContext.append(tempt)
        return len(globalContext)-1
    else:
        pos = globalContext.index(tempt)
        ans.append(pos)
        return pos
def data2Context(pos):
    global globalContext
    return globalContext[pos]
def dataList2Context(dataList):
    global globalContext
    ans = []
    for i in dataList:
        if (i == None):
            ans.append(None)
        else:
            ans.append(globalContext[i])
    return ans
def ActionList(acList, ans):
    global resRepGlobListFlat, rrDataGlobListFlat
    for sigAction in acList:
        sigD = []
        if (sigAction == [] or sigAction == None):
            continue
        resRepGlobListFlat.append(sigAction)
        if (sigAction[0] == "CHECK"):
            pos = addGlobalContext(ans, showConstrain(sigAction[1]), sigAction)
            rrDataGlobListFlat.append(pos)
        elif (sigAction[0] == "FuncCall"):
            tempt = MulList2str(["FuncCall", sigAction[1].name])
            pos = addGlobalContext(ans, tempt, sigAction)
            rrDataGlobListFlat.append(pos)
        elif (sigAction[0] == "Return"):
            tempt = MulList2str(sigAction)
            pos = addGlobalContext(ans, tempt, sigAction)
            rrDataGlobListFlat.append(pos)
        elif (sigAction[0] == "Assign" or sigAction[0] == "Read"):
            tempt = MulList2str(sigAction[:-3])
            pos = addGlobalContext(ans, tempt, sigAction)
            rrDataGlobListFlat.append(pos)
        else:
            tempt = MulList2str(sigAction[:-1])
            pos = addGlobalContext(ans, tempt, sigAction)
            rrDataGlobListFlat.append(pos)
    return ans
def Index2Context(sigIndex):
    global globalContext
    return globalContext[sigIndex]
def PosList2DataList(sortedPosList):
    global rrDataGlobListFlat
    ans = []
    for sigPos in sortedPosList:
        ans.append(rrDataGlobListFlat[sigPos])
    return ans
def TrainProcess(sigGroupList, groupListSources):
    data = []
    gNum = len(sigGroupList)
    for sg in range(gNum):
        sigContext = sigGroupList[sg]
        sigContextSource = groupListSources[sg]
        data.append(sigContext.indexList)
    return data
def rrMatch(a,b):
    if (a == b):
        return True
    else:
        return False
funcTypeDict = {}
def ConsProcess(cons):
    global funcTypeDict, funcCallMark, globalContext
    fmarkLen = len(funcCallMark)
    cLists = cons.split()
    newcList = []
    for sigc in cLists:
        if (IsFuncCall(sigc)):
            fN = sigc[fmarkLen:]
            if (fN in funcTypeDict):
                if (isinstance(funcTypeDict[fN], list)):
                    newcList.append(sigc)
                else:
                    newcList.append(funcTypeDict[fN])
            else:
                newcList.append(sigc)
        elif (InGuardSigList(sigc) == -1):
            newcList.append(sigc)
    return newcList
def ConsFuncEqualProcess(cons):
    global funcEqualSet
    global funcTypeDict, funcCallMark, globalContext
    fmarkLen = len(funcCallMark)
    cLists = cons.split()
    repList = []
    comList = []
    for sigc in cLists:
        if (IsFuncCall(sigc)):
            fN = sigc[fmarkLen:]
            if(fN in funcEqualSet):
                repList.append(funcEqualSet[fN])
            else:
                comList.append(sigc)
        elif (InGuardSigList(sigc) == -1):
            comList.append(sigc)
    ansList = []
    ansList.append(comList)
    for sigR in repList:
        temptList = []
        for siga in ansList:
            siga.append(sigR)
            temptList.append(siga)
        ansList = copy.deepcopy(temptList)
    return ansList
def ConsNormalizeCompare(compos1, compos2):
    global globalContext
    c1 = ConsProcess(globalContext[compos1])
    c2 = ConsProcess(globalContext[compos2])
    if (set(c1)==set(c2)):
        return True
    else:
        return False
funcEqualSet = {}
def FuncReplaceCompare(compos1, compos2):
    c1List = ConsFuncEqualProcess(globalContext[compos1])
    c2List = ConsFuncEqualProcess(globalContext[compos2])
    for sigc1 in c1List:
        for sigc2 in c2List:
            if (set(sigc1)==set(sigc2)):
                return True
    return False
def AndOrCheck(constrain, targetCons):
    if (len(constrain) == 3 and constrain[1] == "&&"):
        if (len(constrain[0])==3 and constrain[0][1] == "&&"):
            f1 = AndOrCheck(constrain[0], targetCons)
            if (f1):
                return True
        else:
            ncons = ConstrantNormalize(copy.deepcopy(constrain[0]))
            nc = showConstrain(ncons[0])
            if (globalContext[targetCons] == nc):
                return True
            else:
                c1 = ConsProcess(globalContext[targetCons])
                c2 = ConsProcess(nc)
                if (set(c1) == set(c2)):
                    return True
        if (len(constrain[2])==3 and constrain[2][1] == "&&"):
            f2 = AndOrCheck(constrain[2], targetCons)
            if (f2):
                return True
        else:
            ncons = ConstrantNormalize(copy.deepcopy(constrain[2]))
            nc = showConstrain(ncons)
            if (globalContext[targetCons] == nc):
                return True
            else:
                c1 = ConsProcess(globalContext[targetCons])
                c2 = ConsProcess(nc)
                if (set(c1) == set(c2)):
                    return True
    return False
funcRep = {}
def FuncProp(patternP, curP):
    global funcRep, globalContext
    fmarkLen = len(funcCallMark)
    first = globalContext[patternP]
    fLists = first.split()
    firstList = []
    for sigc in fLists:
        if (IsFuncCall(sigc)):
            fN = sigc[fmarkLen:]
            firstList.append(fN)
    second = globalContext[curP]
    sLists = second.split()
    secondList = []
    for sigc in sLists:
        if (IsFuncCall(sigc)):
            fN = sigc[fmarkLen:]
            secondList.append(fN)
    if (firstList!=[] and secondList!=[]):
        for sigf in firstList:
            if (sigf in funcRep):
                for sigs in secondList:
                    if (sigs in funcRep[sigf]):
                        return True
    return False
def funcRepAdd(a, b):
    global funcRep
    if a in funcRep:
        funcRep[a].append(b)
    else:
        funcRep[a] = [b]
def findConstrain(cons, sRange, funcName, patternPos):
    global EHDataList, EHRRList, globalContext
    for i in sRange:
        if (EHRRList[i][0]=="CHECK" or EHRRList[i][0]=="Assert CHECK"):
            if (cons == EHDataList[i]):
                return True
            elif (ConsNormalizeCompare(cons, EHDataList[i])):
                return True
            elif (AndOrCheck(EHRRList[i][2][0], cons)):
                return True
        elif (EHRRList[i][0]=="FuncCall"):
            fN = EHRRList[i][1].name
            if (fN == funcName):
                continue
            if (fN not in funcSuspiciousDict):
                continue
            addFrom = funcSuspiciousDict[fN]
            addFromNum = len(addFrom)
            for siga in range(addFromNum):
                sigadd = addFrom[siga]
                if (sigadd[0] == patternPos):
                    for sigit in sigadd[1]:
                        if (sigit[1] == []):
                            return True
    return False
def MultiConcat(itemFirst, addList):
    ansList = []
    if(addList == []):
        return [itemFirst]
    for sigAdd in addList:
        ansList.append(SigConcat(itemFirst, sigAdd))
    return ansList
def SigConcat(itemA, itemB):
    temptI = itemA[1].copy() + itemB[1].copy()
    if (itemA[0] == False):
        return [itemA[0], temptI]
    elif (itemB[0] == False):
        return [itemB[0], temptI]
    if (itemA[0] == None):
        return [itemB[0], temptI]
    else:
        if (itemB[0]!=None):
            print("Debug Error SigConcat")
            print("itemA", itemA)
            print("itemB", itemB)
        else:
            return [itemA[0], temptI]
def ExtendMatchInFunc(funcName, fN, patternPos, curPos, sigItem):
    global funcSuspiciousDict
    global EHPosList
    ansList = []
    ansPathList = []
    if (fN not in funcSuspiciousDict):
        return [], []
    addFrom = funcSuspiciousDict[fN]
    addPathFrom = funcSuspiciousCallPathDict[fN]
    addList = []
    addPathList = []
    addNum = len(addFrom)
    for siga in range(addNum):
        sigadd = addFrom[siga]
        sigaddPath = addPathFrom[siga]
        if (sigadd[0] == patternPos):
            tN = len(sigadd[1])
            for sigt in range(tN):
                sigit = sigadd[1][sigt]
                if (sigit[1] == []):
                    if (curPos == EHPosList[patternPos]):
                        addList.append(sigit)
                        funcSuspiciousAccessDict[fN][siga][sigt] = 1
                        addPathList.append(sigaddPath[sigt])
                elif (sigit[1][0][0] == curPos):

                    addList.append(sigit)
                    funcSuspiciousAccessDict[fN][siga][sigt] = 1
                    addPathList.append(sigaddPath[sigt])
    if (sigItem[0] == -1):
        ansList = addList
    else:
        ansList = MultiConcat(sigItem, addList)
    if (ansList == []):
        ansPathList = []
    else:
        ansPathList = CallPathCombine([[funcName]], addPathList)
    return ansList, ansPathList
def BJumpListForm(jumpList):
    jNum = len(jumpList)
    bJumpList = [None for _ in range(jNum)]
    for i in range(jNum):
        if (jumpList[i]!=None):
            bJumpList[jumpList[i][1]] = [jumpList[i][0], i]
    return bJumpList
def searchRangeReach(targetPos):
    global EHRRMap
    tempList = [targetPos]
    ansList = []
    while (len(tempList)!=0):
        newtemp = []
        for i in tempList:
            for eachi in EHRRMap[i]:
                if (eachi not in ansList and eachi!=targetPos):
                    newtemp.append(eachi)
                    ansList.append(eachi)
        tempList = newtemp
    return ansList
def SigCallPathCombine(beforePath, afterPath):
    ansPath = beforePath.copy()
    for sigap in afterPath:
        if sigap not in ansPath:
            ansPath.append(sigap)
    return ansPath
def CallPathCombine(beforeList, afterList):
    if (afterList == []):
        return beforeList
    newAnsList = []
    for sigb in beforeList:
        for sigf in afterList:
            newAnsList.append(SigCallPathCombine(sigb, sigf))
    return newAnsList
def WindowMatch(funcName, patternPos, pattern, pos, constrain, patternStart, patternEnd, curPatternPos, rrRange):
    global EHRRList, EHDataList, EHJumpList
    if (list(rrRange) == [] or rrRange[0] > rrRange[-1]):
        return [], []
    rrNum = len(EHRRList)
    patternNum = len(pattern)
    ansList = []
    callPathList = []
    sigans = []
    if (curPatternPos>=patternEnd):
        return ansList, callPathList
    if (len(EHDataList)!=len(EHJumpList)):
        print("Error 2 Len is not match WindowMatch")
    rrn = len(rrRange)
    for rrni in range(rrn):
        j = rrRange[rrni]
        if (rrMatch(pattern[curPatternPos], EHDataList[j])):
            for nji in range(rrni+1, rrn):
                nj = rrRange[nji]
                if (rrMatch(pattern[curPatternPos], EHDataList[nj])):
                    if (curPatternPos+1 != patternEnd):
                        rrRangeOld = searchRangeReach(rrni)
                        rrRangeNew = searchRangeReach(nj)
                        sigansNew = copy.deepcopy(sigans)
                        sigans.append([curPatternPos, j, EHDataList[j], globalContext[EHDataList[j]], funcName])
                        sigansNew.append([curPatternPos, nj, EHDataList[nj], globalContext[EHDataList[nj]], funcName])
                        resultOld = sigAnsCheck(sigans, pos, constrain, rrRange, funcName, patternPos, j)
                        resultNew = sigAnsCheck(sigansNew, pos, constrain, rrRange, funcName, patternPos, nj)
                        curPatternPos += 1
                        if (resultOld==False):
                            ansList.append([resultOld, sigans])
                            callPathList.append([funcName])
                        else:
                            backold, backOldCallPath = WindowMatch(funcName, patternPos, pattern, pos, constrain, patternStart, patternEnd, curPatternPos, rrRangeOld)
                            if (resultOld == -1):
                                ansList.extend(backold)
                            else:
                                sigExt = MultiConcat([resultOld, sigans], backold)

                                ansList.extend(sigExt)
                            nPathList = CallPathCombine([[funcName]], backOldCallPath)
                            callPathList.extend(nPathList)
                        if (resultNew==False):
                            ansList.append([resultNew, sigansNew])
                            callPathList.append([funcName])
                        else:
                            backnew, backNewCallPath = WindowMatch(funcName, patternPos, pattern, pos, constrain, patternStart, patternEnd, curPatternPos, rrRangeNew)
                            if (resultOld == -1):
                                ansList.extend(backnew)
                            else:
                                sigExt = MultiConcat([resultOld, sigansNew], backnew)
                                ansList.extend(sigExt)
                            nPathList = CallPathCombine([[funcName]], backNewCallPath)
                            callPathList.extend(nPathList)
                        return ansList, callPathList
                    else:
                        sigans.append([curPatternPos, j, EHDataList[j], globalContext[EHDataList[j]], funcName])
                        result = sigAnsCheck(sigans, pos, constrain, rrRange, funcName, patternPos, j)
                        curPatternPos += 1
                        if (result == -1):
                            ansList = []
                            callPathList = []
                        elif (result == False):
                            ansList = [[result, sigans]]
                            callPathList = [[funcName]]
                        else:
                            ansList = [[result, sigans]]
                            callPathList = [[funcName]]
                        return ansList, callPathList
            sigans.append([curPatternPos, j, EHDataList[j], globalContext[EHDataList[j]], funcName])
            curPatternPos = curPatternPos + 1
            if (curPatternPos == patternEnd):
                break
        elif (EHRRList[j][0] == "FuncCall"):
            fN = EHRRList[j][1].name
            result = sigAnsCheck(sigans, pos, constrain, rrRange, funcName, patternPos, j)
            if (result == False):
                return [[result, sigans]], [[funcName]]
            backRRRange = list(range(j + 1, rrRange[-1] + 1))
            if (fN != funcName):
                exList, exPathList = ExtendMatchInFunc(funcName, fN, patternPos, curPatternPos, [result, sigans])
                for sigex in range(len(exList)):
                    sigExList = exList[sigex]
                    sigExPathList = exPathList[sigex]
                    if (sigExList[1] != []):
                        cPos = sigExList[1][-1][0]+1
                        if (sigExList[0] == None and cPos==patternNum):
                            fRange = range(j+1, rrNum)
                            if (findConstrain(constrain, fRange, funcName, patternPos)==True):
                                sigExList[0] = False
                        back, backPathList = WindowMatch(funcName, patternPos, pattern, pos, constrain, patternStart, patternEnd, cPos, backRRRange)
                        sigExt = MultiConcat(sigExList, back)
                        ansList.extend(sigExt)
                        ncallPathList = CallPathCombine([sigExPathList], backPathList)
                        callPathList.extend(ncallPathList)
                    else:
                        ansList.append([False, sigans])
                        callPathList.append([funcName])
            back, bPathList = WindowMatch(funcName, patternPos, pattern, pos, constrain, patternStart, patternEnd, curPatternPos, backRRRange)
            if(back != None):
                if (result == -1):
                    ansList.extend(back)
                else:
                    sigExt = MultiConcat([result, sigans], back)
                    ansList.extend(sigExt)
                nPathList = CallPathCombine([[funcName]], bPathList)
                callPathList.extend(nPathList)
            return ansList, callPathList
        if (EHJumpList[j]!=None):
            if(EHRRList[j][0] != "CHECK" or EHRRList[j][5]==-1):
                print("Error!: wrong jumpList", flush=True)
                continue
            result = sigAnsCheck(sigans, pos, constrain, rrRange, funcName, patternPos, j)
            if (result == False):
                return [[result, sigans]], [[funcName]]
            rrRange1 = list(range(j+1, EHJumpList[j][0]))
            rrRange1.extend(list(range(EHJumpList[j][1], rrRange[-1]+1)))
            rrRange1new = searchRangeReach(j)
            rrRange1 = list(set(rrRange1).intersection(set(rrRange1new)))
            rrRange2 = range(EHJumpList[j][0]+1, rrRange[-1]+1)
            rrRange2 = list(set(rrRange2).intersection(set(rrRange1new)))
            back1, bPList1 = WindowMatch(funcName, patternPos, pattern, pos, constrain, patternStart, patternEnd, curPatternPos, rrRange1)
            back2, bPList2 = WindowMatch(funcName, patternPos, pattern, pos, constrain, patternStart, patternEnd, curPatternPos, rrRange2)
            addList = []
            addList = back1 + back2
            addPList = bPList1 + bPList2
            if (result == -1):
                return addList, addPList
            ansList = MultiConcat([result, sigans], addList)
            callPathList = CallPathCombine([[funcName]], addPList)
            return ansList, callPathList
    result = sigAnsCheck(sigans, pos, constrain, rrRange, funcName, patternPos, rrNum-1)
    if (result == -1):
        ansList = []
        callPathList = []
    elif (result == False):
        ansList = [[result, sigans]]
        callPathList = [[funcName]]

    else:
        ansList = [[result, sigans]]
        callPathList = [[funcName]]

    return ansList, callPathList
def sigAnsCheck(sigAns, pos, constrain, rRange, funcName, patternPos, curEHRRPos):
    global EHDataList
    rrNum = len(EHDataList)
    rRange = list(range(rrNum))
    num = len(sigAns)
    if (num == 0):
        if(pos == 0):
            findRange = range(curEHRRPos)
            ans = findConstrain(constrain, findRange, funcName, patternPos)
            if (ans==True):
                return False
            else:
                return -1
        return -1
    startP = sigAns[0][0]
    endP = sigAns[-1][0]+1
    if (startP > pos or endP < pos):
        return None
    else:
        start = -1
        end = -1
        possibleFlag = False
        if (startP < pos and pos < endP):
            start = sigAns[0][1]
            end = sigAns[-1][1]
        elif (startP == pos):
            start = rRange[0]
            end = sigAns[0][1]
            possibleFlag = True
        elif (pos == endP):
            start = sigAns[-1][1]
            end = rRange[-1]
            possibleFlag = True
        if (start == -1 or end == -1):
            return -1
        findRange = list(set(range(start, end + 1)).intersection(set(rRange)))
        findRange.sort()
        if (findConstrain(constrain, findRange, funcName, patternPos)):
            return False
        else:
            if (possibleFlag):

                return None
            return True

def sigPatternDetect(funcName, patternNum):
    global EHRRList, EHDataList, EHJumpList
    global EHPatternList, EHPosList, EHConstrainList
    rrNum = len(EHRRList)
    pattern = EHPatternList[patternNum][0]
    constrain = EHPatternList[patternNum][1]
    pos = EHPosList[patternNum]
    pLen = len(pattern)
    ans = []
    ansPathList = []
    for i in range(pLen):
        tempRRRange = range(0, rrNum)
        sigAns, callPathList = WindowMatch(funcName, patternNum, pattern, pos, constrain, i, pLen, i, tempRRRange)
        if(sigAns == None):
            continue
        sigAns = ansCheck(sigAns, pos, pLen)
        ans.extend(sigAns)
        ansPathList.extend(callPathList)
    return ans, ansPathList

def ansCheck(ansList, pos, pLen):
    newAnsList = []
    for siga in ansList:
        if (siga[0] == None):
            startMP = siga[1][0][0]
            endMP = siga[1][-1][0]

            if (startMP<pos and pos<=endMP):
                siga[0] = True
        newAnsList.append(siga)
    return newAnsList
findedBug = []
def addEHBug(patternPos, macthList, callPath):
    global findedBug
    findedBug.append([patternPos, macthList, callPath])
def MachedListCheck(patternPos, ansList, ansPathList):
    global findedBug, EHPatternList, EHPosList
    pNum = len(EHPatternList[patternPos][0])
    constrainPos = EHPosList[patternPos]
    newAnsList = []
    newPathList = []
    hasTrue = False
    ansNum = len(ansList)
    for i in range(ansNum):
        sigAns = ansList[i]
        sigCallPath = ansPathList[i]
        if (sigAns[0] == -1):
            print("Debug Error: MachedListCheck This ans should not reach here")
        if (sigAns[0] == False):
            hasTrue = True
        elif (len(sigAns[1]) == pNum):
            if (constrainPos==0 or constrainPos == pNum):
                newAnsList.append(sigAns)
                newPathList.append(sigCallPath)
            else:
                addEHBug(patternPos, sigAns[1], sigCallPath)
        else:
            newAnsList.append(sigAns)
            newPathList.append(sigCallPath)
    return newAnsList, newPathList, hasTrue
def CustomTypeCheck():
    global EHPatternList, EHCostomMap, findedBug
    pNum = len(EHPatternList)
    fbNum = len(findedBug)
    newFindBug = []
    for i in range(fbNum):
        ppos = findedBug[i][0]
        if (ppos not in EHCostomMap):

            newFindBug.append(findedBug[i])
            continue
        contextList = findedBug[i][1]
        ctNum = len(contextList)
        funcList = []
        for j in range(ctNum):
            func = contextList[j][-1]
            if (func not in funcList):
                funcList.append(func)
        skipFlag = True
        for sigfunc in funcList:
            if (SetGlobalVar(sigfunc)!=False):
                if(CheckSigFunc(ppos)==False):
                    skipFlag = False
                    break
        if (not skipFlag):
            newFindBug.append(findedBug[i])
    findedBug = newFindBug
def CheckSigFunc(patternPos):
    global EHPatternList, EHRRList, EHDataList, EHCostomMap, globalContext
    rrNum = len(EHDataList)
    targetBList = EHCostomMap[patternPos]
    ansFlag = True
    for i in range(rrNum):
        if (TokenMatch(globalContext[EHDataList[i]], targetBList)):
            ansFlag = False
    if (TypeMatch(targetBList)):
        ansFlag = False
    return ansFlag
def TypeMatch(keywordList):
    global EHType
    for sigt in EHType:
        if sigt in keywordList:
            return True
    return False
def TokenMatch(ehText, keywordList):
    tList = ehText.split(" ")
    for sigb in tList:
        if (sigb in keywordList):
            return True
    return False
detectedList = {}
def sigDetect(funcName):
    global EHPatternList, funcSuspiciousDict, funcSuspiciousAccessDict, funcSuspiciousCallPathDict, EHRRList, EHCostomMap, LogEHRRFlag
    if (funcName in detectedList):
        return
    detectedList[funcName] = 1
    pNum = len(EHPatternList)
    ans = []
    ansPathList = []
    if (SetGlobalVar(funcName) == False):
        funcSuspiciousDict[funcName] = []
        funcSuspiciousAccessDict[funcName] = []
        funcSuspiciousCallPathDict[funcName] = []
        return
    if (JumpListCheck()):
        funcSuspiciousDict[funcName] = []
        funcSuspiciousAccessDict[funcName] = []
        funcSuspiciousCallPathDict[funcName] = []
        return
    EHRRNum = len(EHRRList)
    if (LogEHRRFlag):
        print("EHRRNum funcName", funcName, file = debugInfoLogFile)
        for i in range(EHRRNum):
            print("sigEHRR", i, EHRRList[i], file = debugInfoLogFile)
    for i in range(pNum):
        sigAns, sigPathList = sigPatternDetect(funcName, i)
        hasTrue = False
        if (sigAns!=None):
            sigAns, sigPathList, hasTrue = MachedListCheck(i, sigAns, sigPathList)
            if (hasTrue == False):
                temptRange = range(EHRRNum)
                rs = findConstrain(EHPatternList[i][1], temptRange, funcName, i)
                if (rs == True):
                    sigAns.append([False, []])
                    sigPathList.append([funcName])
            ans.append([i, sigAns])
            ansPathList.append(sigPathList)
    funcSuspiciousDict[funcName] = ans
    funcSuspiciousCallPathDict[funcName] = ansPathList
    ansNum = len(ans)
    accessList = []
    for sigIT in range(ansNum):
        temptk = ans[sigIT][1]
        tar = len(temptk)
        tL = [0 for _ in range(tar)]
        accessList.append(tL)
    funcSuspiciousAccessDict[funcName] = copy.deepcopy(accessList)


EHRRList = []
EHDataList = []
EHJumpList = []
EHRRMap = []
EHPatternList = []
EHPosList = []
EHConstrainList = []
EHType = []
def SetGlobalVar(funcName):
    global EHRRList, EHDataList, EHJumpList, EHRRMap, EHType
    if (funcName in funcDefSumDict.keys()):
        _, aInfo, _, _, _, _, _, _, resRepGlobListFlat, dFlatList, jumpList, rrmap, EHType = funcDefSumDict[funcName]
        for siga in aInfo:
            EHType.append(siga[0])
        EHType = list(set(EHType).difference(set(basicTypeList)))
        EHRRList = resRepGlobListFlat
        EHDataList = dFlatList
        EHJumpList = jumpList
        EHRRMap = rrmap
        return True
    else:
        return False
funcSuspiciousDict = {}
funcSuspiciousAccessDict = {}
funcSuspiciousCallPathDict = {}
def EHBugDetect(orderList):
    global funcDefSumDict, nameListForReach, resRepGlobList
    global EHRRList, EHDataList, EHJumpList, EHPatternList, funcSuspiciousDict
    num = len(orderList)
    for i in range(num):
        funcName = nameListForReach[orderList[i]]
        print("\rEHBugDetect:", i, "/", num, funcName, end="        ", flush=True)
        if (funcName not in funcSuspiciousDict):
            sigDetect(funcName)

def JumpListCheck():
    global EHJumpList
    enum = len(EHJumpList)
    bestDeep = 0
    for i in range(enum):
        if (EHJumpList[i]!=None):
            newdeep = JumDeepCount(i, EHJumpList[i][1], 1)
            bestDeep = max(newdeep, bestDeep)
    if (bestDeep>=4):
        return True
    return False
def JumDeepCount(start, endpos, deep):
    global EHJumpList
    bestDeep = deep
    for i in range(start+1, endpos):
        if (EHJumpList[i]!=None):
            newdeep = JumDeepCount(i, EHJumpList[i][1], deep + 1)
            bestDeep = max(newdeep, bestDeep)
    return bestDeep
def searchPos(nums, target):
    left = 0
    right = len(nums)
    while left < right:
        middle = (left + right) // 2
        if nums[middle] < target:
            left = middle + 1
        elif nums[middle] > target:
            right = middle
        else:
            return middle
    return right-1
def showContext(contextList):
    ansList = []
    for sigContext in contextList:
        if (sigContext == None or sigContext == -1):
            ansList.append(None)
        else:
            ansList.append(Index2Context(sigContext))
    return ansList
def PatternShow(patternList):
    for sigP in patternList:
        print("sigP", sigP)
        print("PatternShow Context", showContext(sigP[0]))
        print("PatternShow Constrain", showConstrain(sigP[1]))
        print("PatternShow Constrain Detail", sigP[1])
def SimilarEHFind(orderList):
    global EHContentReturn, EHContentFuncCall, TotalContentReturn, funcCallNumDict, nameListForReach
    frequentReturn = sorted(EHContentReturn.items(), key=lambda x: x[1])
    frequentFuncCall = sorted(EHContentFuncCall.items(), key=lambda x: x[1])
    addList = []
    for returnKey, returnValue in frequentReturn:
        if(returnKey==""):
            continue
        else:
            addList.append(returnKey)
    num = len(orderList)
    for i in range(num):
        sigfunc = nameListForReach[orderList[i]]
        if (sigfunc not in funcDefSumDict):
            continue
        temptPosList = []
        returnList, rPosList, rMarkList = funcDefSumDict[sigfunc][4:7]
        argInfo = funcDefSumDict[sigfunc][1]
        rNum = len(rMarkList)
        for i in range(rNum):
            if (rMarkList[i] != 1 and rMarkList[i]!=-1):
                if (returnList[i].norm == [["__HardCodedVar__"]]):
                    temptStr = BList2String(returnList[i].bList)
                    if (temptStr in addList):
                        temptPosList.append(rPosList[i])
        BackGroundSet(sigfunc)
        imptC, _ = EHProcess(temptPosList, argInfo)
        imptC = meteralDivide(imptC, sigfunc + "SimilarEHFind")
        funcDefSumDict[sigfunc][7].extend(imptC)
relationLen  = 0
EHCostomMap = {}
funcDefOrder = []
def PatternMark():
    global EHPatternList, EHPosList, EHConstrainList
    global EHCostomMap
    EHCostomMap = {}
    ehNum = len(EHPatternList)
    for i in range(ehNum):
        guardInfo = globalContext[EHPatternList[i][1]]
        ansList = TokenCheck(guardInfo)
        if (ansList!=None):
            EHCostomMap[i] = ansList
def ProjectBasicInfo(projectName, path, fileTypes, funcFilterThreshold):
    global tokenList, typeList, relation, childRange, relationLen
    global funcDefInfoDict, funcDefSumDict, funcTypeDict
    global EHPatternList, EHPosList, EHConstrainList
    global detectedList
    global EHContentReturn, EHContentFuncCall, TotalContentReturn
    global funcCallNumDict
    global GlobalResNameList, GlobalResTypeList
    global fileTreeList, funcDefOrder, studyMeteral, studyMeteralSource, funcBackGround, funcContextDict, funcEHEXList, funcEqualSet
    global funcSuspiciousDict, funcSuspiciousAccessDict, funcSuspiciousCallPathDict, funcLearnedContextDict
    funcSuspiciousDict = {}
    funcSuspiciousAccessDict = {}
    funcSuspiciousCallPathDict = {}
    funcLearnedContextDict = {}
    detectedList = {}
    funcEqualSet = {}
    funcBackGround = {}
    funcContextDict = {}
    funcEHEXList = []
    fileList, codeList, fileTypeList = getCode(path, fileTypes)
    fileTreeList = []
    studyMeteral = []
    studyMeteralSource = []
    codeNum = len(codeList)
    GlobalResNameList = []
    GlobalResTypeList = []
    EHContentReturn = {}
    EHContentFuncCall = {}
    TotalContentReturn = {}
    funcTypeDict = {}
    funcCallNumDict = {}
    funcDefInfoDict = {}
    funcDefSumDict = {}
    for i in range(codeNum):
        print("\rProjectBasicInfo code:", i, "/", codeNum, end="        ", flush=True)
        code = codeList[i]
        codes = code.split("\n")
        lineNum = len(codes)
        if (lineNum > 500):
            continue
        fileP = len(fileTreeList)
        tree = genTree(code, "c")
        relation, typeList, tokenList, childRange = TreeProc(tree, codes)
        relationLen = len(relation)
        fileTreeList.append((tokenList, typeList, relation))
        nameList, posList, funcTypeList, callList = CallGraph(fileP)
        n = len(nameList)
        for j in range(n):
            if nameList[j] not in funcDefInfoDict.keys():
                funcDefInfoDict[nameList[j]] = [posList[j], funcTypeList[j], callList[nameList[j]]]
                funcTypeDict[nameList[j]] = funcTypeList[j]
    funcDefOrder, skipList, nameListForReach, groupedList = FuncCallGraphAnalysis()
    orderNum = len(funcDefOrder)
    CHECKFuncEXList = []
    FunDetailAnalysis(funcDefOrder)
    MoreEHFind()
    SimilarEHFind(funcDefOrder)
    FuncContextStudy(reversed(funcDefOrder))
    EHExtend()
    patternList, posList, constrainList, supportNum, debugDataList = MeteTrain()
    patternList, posList, constrainList = PatternFilt(patternList, posList, constrainList, supportNum, debugDataList, funcFilterThreshold)
    save_variables(projectName, patternList, posList, constrainList)

def EHBugDetection(project_name, path):
    global EHPatternList, EHPosList, EHConstrainList, funcDefOrder, findedBug
    findedBug = []
    EHPatternList, EHPosList, EHConstrainList = load_and_concatenate(project_name)
    PatternMark()
    EHBugDetect(funcDefOrder)
    EHBugMore(funcDefOrder)
    EHBugShow(path)


def EHBugMore(orderList):
    global funcSuspiciousAccessDict, funcSuspiciousDict, nameListForReach
    global EHPatternList
    num = len(orderList)
    for i in range(num):
        funcName = nameListForReach[orderList[i]]
        if (funcName in funcSuspiciousDict):
            addFromList = funcSuspiciousDict[funcName]
            addMarkList = funcSuspiciousAccessDict[funcName]
            addNum = len(addFromList)
            for j in range(addNum):
                tList = addFromList[j][1]
                tNum = len(tList)
                for sigt in range(tNum):
                    if (addMarkList[j][sigt] == 0):
                        patternPos = addFromList[j][0]
                        curPatternSize = len(EHPatternList[patternPos][0])
                        sigAC = tList[sigt]
                        if (sigAC[0] == None and len(sigAC[1]) == curPatternSize):
                            addEHBug(patternPos, sigAC[1], funcSuspiciousCallPathDict[funcName][j])

normalCMPToken = ["CMP", "__HardCodedVar__", "Read", "Assign", "&&", "||", "&", "|"]
def TokenCheck(tk):
    global normalCMPToken, basicTypeList
    ansList = []
    tkList = tk.split(" ")
    for i in tkList:
        if (len(i)>15 and i[:15] == "**_FUNC_CALL_**"):
            continue
        if i not in normalCMPToken and i not in basicTypeList:
            ansList.append(i)
    if(ansList == []):
        return None
    else:
        return ansList
def AbnormalGuardRemove(guardInfo):
    gList = guardInfo.split(" ")
    if ("CMP" in gList):
        gPos = gList.index("CMP")

        if ("__HardCodedVar__" in gList[:gPos] and len(gList[:gPos])>1):
            return True
        if ("__HardCodedVar__" in gList[gPos+1:] and len(gList[gPos+1:])>1):
            return True
        return False
    else:
        return True
def PatternFilt(patternList, posList, constrainList, supportNum, debugDataList, funcFilterThreshold):
    global funcCallNumDict, normalCMPToken
    pNum = len(patternList)
    checkedList = [0 for _ in range(pNum)]
    ansList = []
    for i in range(pNum):
        if (checkedList[i] == 0):
            checkedList[i] = 1
            temptList = [i]
            for j in range(i+1, pNum):
                if (patternList[i][0] == patternList[j][0]):
                    checkedList[j] = 1
                    temptList.append(j)
            tNum = len(temptList)
            if (tNum) == 1:
                ansList.append(temptList[0])
            else:
                best = temptList[0]
                bestSupport = supportNum[best]
                for sigt in temptList:
                    if (supportNum[sigt]>bestSupport):
                        bestSupport = supportNum[sigt]
                        best = sigt
                ansList.append(best)
    newAnsList = []
    for i in ansList:
        conList = dataList2Context(patternList[i][0])
        guardInfo = globalContext[patternList[i][1]]
        fNList = []
        cFlag = True
        customFlag = False
        for eachitem in conList:
            if (len(eachitem)>8 and eachitem[:8] == "FuncCall"):
                fNList.append(eachitem[9:])
            else:
                if (TokenCheck(eachitem)!=None):
                    customFlag = True
        if (not customFlag and TokenCheck(guardInfo)!=None):
            customFlag = True
        beforeLen = len(fNList)
        if (len(set(fNList))<beforeLen):
            cFlag = False
        else:
            if (not customFlag):
                if (beforeLen == 1):
                    fN = fNList[0]
                    if ((fN in funcCallNumDict) and (funcCallNumDict[fN] * funcFilterThreshold -1 >= supportNum[i])):
                        cFlag = False
                elif (beforeLen>1):
                    allFlag = False
                    for fN in fNList:
                        if ((fN in funcCallNumDict) and (funcCallNumDict[fN] * funcFilterThreshold <= supportNum[i])):
                            allFlag = True
                    if (not allFlag):
                        cFlag = False
        if (AbnormalGuardRemove(guardInfo)):
            cFlag = False
        if (cFlag):
            newAnsList.append(i)
    nnansList = []
    for i in newAnsList:
        if (len(patternList[i][0]) == 1):
            templ = globalContext[patternList[i][0][0]].split(" ")

            if (templ[0] == "Read" and len(templ) == 2):
                continue
        nnansList.append(i)
    newAnsList = nnansList
    newPatternList = []
    newPosList = []
    newConstrainList = []
    newDebugDataList = []
    for i in newAnsList:
        newPatternList.append(patternList[i])
        newPosList.append(posList[i])
        newConstrainList.append(constrainList[i])
        newDebugDataList.append(debugDataList[i])
    if (LogEHRRFlag):
        PatternOutPut(patternList, posList, constrainList, supportNum, debugDataList, ansList, newAnsList)
    return newPatternList, newPosList, newConstrainList

def PatternOutPut(patternList, posList, constrainList, supportNum, debugDataList, ansList, newAnsList):
    patternLogFile = open(DebugPatternPath, 'w')
    for i in newAnsList:
        print("===================================Pattern===================================", file=patternLogFile)
        print("Context", dataList2Context(patternList[i][0]), file=patternLogFile)
        print("Guard", globalContext[patternList[i][1]], file=patternLogFile)
        print("Pos", posList[i], file=patternLogFile)
        print("supportNum", supportNum[i], file=patternLogFile)
        for j in range(supportNum[i]):
            print("TrainMete sig", dataList2Context(debugDataList[i][0][j]), file=patternLogFile)
            print("TrainMete From", debugDataList[i][1][j], file=patternLogFile)
    deleted = list(set(ansList)-set(newAnsList))
    print("Delete ", len(deleted), " Pattern")
    for i in deleted:
        print("===================================Deleted Pattern===================================", file=patternLogFile)
        print("Context", dataList2Context(patternList[i][0]), file=patternLogFile)
        print("Guard", globalContext[patternList[i][1]], file=patternLogFile)
        print("Pos", posList[i], file=patternLogFile)
        print("supportNum", supportNum[i], file=patternLogFile)
        for j in range(supportNum[i]):
            print("TrainMete sig", dataList2Context(debugDataList[i][0][j]), file=patternLogFile)
            print("TrainMete From", debugDataList[i][1][j], file=patternLogFile)
    return
def EHExtend():
    global funcLearnedContextDict
    global funcDefSumDict
    for sigF in funcDefSumDict:
        curEH = funcDefSumDict[sigF][7]
        for sigCons in curEH:
            newCap = sigCons
            if (newCap.upDataList[0]!=None and newCap.upDataList[0]!=-1):
                print("Debug Error: EHExtend have dataList not have need extend")
            if (funcLearnedContextDict[sigF] != []):
                newCap.NewUpAdd(copy.deepcopy(funcLearnedContextDict[sigF][0]))
            else:
                newCap.upDataList = newCap.upDataList[1:]
                newCap.GenIndexList()
            AddNewMeteral(newCap, sigF+" EHExtend")

funcLearnedContextDict = {}
def FuncContextStudy(orderList):
    global funcContextDict, funcLearnedContextDict, nameListForReach, funcCallNumDict
    for sigi in orderList:
        sigFunc = nameListForReach[sigi]
        if (sigFunc not in funcContextDict):
            funcLearnedContextDict[sigFunc] = []
            continue
        fData, fContexts = funcContextDict[sigFunc]
        fContexts = FuncNeedExtendProc(fContexts)
        fcontextList = GroupStudy(fContexts, fData)
        if (fcontextList != None):
            if (fData not in fcontextList):
                print("Debug Error: The FuncCall itself is not in here")
            tempP = fcontextList.index(fData)
            funcLearnedContextDict[sigFunc] = [fcontextList[:tempP], fcontextList[tempP+1:]]
        else:
            print("Debug Error: not learned pre")
def FuncNeedExtendProc(fContexts):
    ansList = []
    for sigf, contextData in fContexts:
        if contextData[0]!= -1:
            ansList.append(contextData)
        elif (sigf in funcLearnedContextDict and len(funcLearnedContextDict[sigf]) == 2):
            ansList.append(funcLearnedContextDict[sigf][0]+contextData[1:] + funcLearnedContextDict[sigf][1])
        else:
            ansList.append(contextData[1:])
    return ansList
def EHBugShow(path):
    global findedBug, EHPatternList, EHPosList
    CustomTypeCheck()
    newFindedBug = []
    bNum = len(findedBug)
    if bNum == 0:
        print("Not find any bug")
        return
    findedBug = sorted(findedBug, key=lambda x: x[0])
    newFindedBug = [findedBug[0]]
    if (CallPathDiff):
        for i in range(1, bNum):
            if (findedBug[i] not in newFindedBug):
                newFindedBug.append(findedBug[i])
    else:
        matchRecord = [findedBug[0][1]]
        for i in range(1, bNum):
            if (findedBug[i][1] not in matchRecord):
                newFindedBug.append(findedBug[i])
                matchRecord.append(findedBug[i][1])
    findedBug = newFindedBug
    bNum = len(findedBug)
    print("Finded", bNum, "EH bugs")
    with open(FindedBugPath, 'w') as f:
        print("Finded:", bNum, " EH bugs", file=f)
        if (bNum>0):
            curPatternPos = findedBug[0][0]
            curi = 1
            last = 0
            while(curi<bNum):
                if (findedBug[curi][0] == curPatternPos):
                    curi = curi + 1
                else:
                    curp = EHPatternList[curPatternPos]
                    print(curi-last, "matched Bug pattern", curPatternPos, file=f)
                    print("Content", showContext(curp[0]), file=f)
                    print("CHECK", globalContext[curp[1]], file=f)
                    print("Pos", EHPosList[curPatternPos], file=f)
                    curPatternPos = findedBug[curi][0]
                    for j in range(last, curi):
                        print("Matched part", findedBug[j][1], file=f)
                        print("Call Graph", findedBug[j][2], file=f)
                    last = curi
                    curi = curi + 1
            curp = EHPatternList[curPatternPos]
            print(curi-last, "matched Bug pattern", curPatternPos, file=f)
            print("Content", showContext(curp[0]), file=f)
            print("CHECK", globalContext[curp[1]], file=f)
            print("Pos", EHPosList[curPatternPos], file=f)
            for j in range(last, curi):
                print("Matched part", findedBug[j][1], file=f)
                print("Call Graph", findedBug[j][2], file=f)
def ChildrenList(pos):
    global relationLen, relation
    cList = []
    for i in range(pos + 1, relationLen):
        if (relation[i] == pos):
            cList.append(i)
            cList.extend(ChildrenList(i))
    return cList
def DirectChildrenList(pos):
    global relation, relationLen
    cList = []
    for i in range(pos + 1, relationLen):
        if (relation[i] == pos):
            cList.append(i)
    return cList
def SonList(pos):
    global relation, relationLen
    sonList = []
    for i in range(pos + 1, relationLen):
        if (relation[i] == pos):
            sonList.append(i)
    return sonList
def ErrorLogMatch(i):
    for sigPatternList in paternList:
        flag = 1
        for sigKeyWord in sigPatternList:
            if sigKeyWord not in tokenList[i]:
                flag = 0
                break
        if (flag == 1):
            return 1
    return 0
def PatternMatch(sigFunCall):
    content = sigFunCall.content
    for sigPatternList in paternList:
        flag = 1
        for sigKeyWord in sigPatternList:
            if sigKeyWord not in content:
                flag = 0
                break
        if (flag == 1):
            return 1
    return 0
def TypeFind(nodeStartPos, type):
    num = len(typeList)
    for i in range(nodeStartPos + 1, num):
        if typeList[i] == type:
            return i
    return -1
def TypeFindInList(targetList, type):
    for i in targetList:
        if typeList[i] == type:
            return i
    return -1
def TypesFindAllInList(targetList, types):
    ansList = []
    for i in targetList:
        if typeList[i] in types:
            ansList.append(i)
    return ansList
def TypeFindAllInList(targetList, type):
    ansList = []
    for i in targetList:
        if typeList[i] == type:
            ansList.append(i)
    return ansList
def TypesFindInList(targetList, types):
    for i in targetList:
        if typeList[i] in types:
            return i
    return -1
def TypeFindInSubTree(fatherNode, type):
    global relation, relationLen
    if (fatherNode>=relationLen):
        return [], None
    sPos = fatherNode + 1
    ePos = RangeEndPosFind(fatherNode)
    cList = range(sPos, ePos + 1)
    if (len(cList)<=0):
        return [], None
    subTreeList = []
    for i in cList:
        if typeList[i] == type:
            subTreeList.append(i)
    return subTreeList, ePos
def TypeFindNameInSubTree(fatherNode, type):
    sPos = fatherNode + 1
    ePos = RangeEndPosFind(fatherNode)
    cList = range(sPos, ePos + 1)
    if (len(cList) <= 0):
        return [], None
    subTreeList = []
    subTreeNameList = []
    for i in cList:
        if typeList[i] == type:
            subTreeList.append(i)
            subTreeNameList.append(tokenList[i])
    return subTreeList, subTreeNameList, ePos
def TypesFindInSubTree(fatherNode, types):
    sPos = fatherNode + 1
    ePos = RangeEndPosFind(fatherNode)
    cList = range(sPos, ePos + 1)
    if (len(cList) <= 0):
        return [], None
    subTreeList = []
    for i in cList:
        if typeList[i] in types:
            subTreeList.append(i)
    return subTreeList, ePos
def TypesFindFirstInSubTree(fatherNode, types):
    sPos = fatherNode + 1
    ePos = RangeEndPosFind(fatherNode)
    cList = range(sPos, ePos + 1)
    if (len(cList) <= 0):
        return None, ePos
    subTreeList = []
    for i in cList:
        if typeList[i] in types:
            return i, ePos
    return None, ePos
def TypeFindFirstInSubTree(fatherNode, type):
    global relation, relationLen
    sPos = fatherNode + 1
    ePos = RangeEndPosFind(fatherNode)
    cList = range(sPos, ePos + 1)
    for i in cList:
        if typeList[i] == type:
            return i, ePos
    return None, ePos
def TypeFindInDirectSubTree(pos, type):
    tL = DirectChildrenList(pos)
    for sigT in tL:
        if (typeList[sigT] == type):
            return sigT
    return None
def GlobalVarLoad():
    global globalContext
    globalContext = VarLoad("globalContext")
def GlobalVarSave():
    global globalContext
    globalContext = VarSave(globalContext, "globalContext")
def StructBackTrack(proNameList, projectPathList, patternListList, BasicPath, fileTypes, funcFilterThreshold, detail = True, ):

    global funcDefSumDict, nameListForReach, resRepGlobList, workingDir
    global EHRRList, EHDataList, EHJumpList, funcSuspiciousDict
    global funcDefOrder, funcSuspiciousAccessDict, funcSuspiciousCallPathDict, globalContext, setGlobalContext

    num = len(projectPathList)
    global paternList
    if (setGlobalContext):

        globalContext = VarLoad(workingDir+"/GlobalContext/globalContext")
    for i in range(num):

        paternList = patternListList[i]
        SetLogEnv(proNameList[i])
        GlobalVarLoad()
        if (DetailAnalysis):
            ProjectBasicInfo(proNameList[i], projectPathList[i], fileTypes, funcFilterThreshold)
            save_project(proNameList[i],  funcDefSumDict, nameListForReach, resRepGlobList, EHRRList, EHDataList, EHJumpList, funcSuspiciousDict, funcDefOrder, funcSuspiciousAccessDict, funcSuspiciousCallPathDict, globalContext)
        else:
            varDict = load_variables(proNameList[i])
            funcDefSumDict = varDict["funcDefSumDict"]
            nameListForReach = varDict["nameListForReach"]
            resRepGlobList = varDict["resRepGlobList"]
            EHRRList = varDict["EHRRList"]
            EHDataList = varDict["EHDataList"]
            EHJumpList = varDict["EHJumpList"]
            funcSuspiciousDict = varDict["funcSuspiciousDict"]
            funcDefOrder = varDict["funcDefOrder"]
            funcSuspiciousAccessDict = varDict["funcSuspiciousAccessDict"]
            funcSuspiciousCallPathDict = varDict["funcSuspiciousCallPathDict"]
            if (not setGlobalContext):
                globalContext = varDict["globalContext"]
        StructCode = EHBugDetection(proNameList[i], projectPathList[i])
        GlobalVarSave()
DebugPatternPath = ""
DebugRRInfoLogPatch = ""
FindedBugPath = ""
debugInfoLogFile = None
def SetLogEnv(proName):
    global DebugPatternPath, DebugRRInfoLogPatch, FindedBugPath, debugInfoLogFile, workingDir
    p = proName.index("-")
    FolderName = workingDir + "/TestResult/" + proName[:p] + "/"
    curFileName = proName[p+1:]
    DebugPatternPath = FolderName + "Pattern " + curFileName + ".txt"
    DebugRRInfoLogPatch = FolderName + "RRInfo " + curFileName + ".txt"
    FindedBugPath = FolderName + "Finded Bug " + curFileName + ".txt"
    if not os.path.exists(FolderName):
        os.makedirs(FolderName)
    debugInfoLogFile = open(DebugRRInfoLogPatch, 'a')

def runTest():
    global MeteTrainMinGroupNum, VarTrainMinGroupNum, OnlyReadFlag, CallPathDiff, LogEHRRFlag, DetailAnalysis, setGlobalContext, cmdRun
    sTime = time.time()
    pPathList, projectPathList, patternListList, BasicPath, fileTypes, funcFilterThreshold = ConfigFunc()
    print("Config complete")
    StructBackTrack(pPathList, projectPathList, patternListList, BasicPath, fileTypes, funcFilterThreshold, False)
    eTime = time.time()
    print("Time cost:", eTime - sTime)
runTest()
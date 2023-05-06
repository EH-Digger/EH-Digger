import pickle, os
from ConfigFile import varSavePath, projectSavePath
from ConfigFile import loadAllVarFlag

def VarSave(var, varName):
    fileName = varName + ".pickle"
    with open(fileName, "wb") as f:
        pickle.dump(var, f)

def VarLoad(varPath):
    loaded_variable = []
    if (os.path.exists(varPath)):
        with open(varPath, "rb") as f:
            loaded_variable = pickle.load(f)
    return loaded_variable

def save_variables(project_name, a, b, c):
    project_path = os.path.join(varSavePath, project_name)
    if not os.path.exists(project_path):
        os.makedirs(project_path)

    file_name_a = "patternList.pickle"
    file_name_b = "posList.pickle"
    file_name_c = "constrainList.pickle"

    with open(os.path.join(project_path, file_name_a), 'wb') as f:
        pickle.dump(a, f)

    with open(os.path.join(project_path, file_name_b), 'wb') as f:
        pickle.dump(b, f)

    with open(os.path.join(project_path, file_name_c), 'wb') as f:
        pickle.dump(c, f)

def load_and_concatenate(curProjectName):
    global varSavePath
    ta = []
    tb = []
    tc = []
    if loadAllVarFlag:
        for project_name in os.listdir(varSavePath):
            project_path = os.path.join(varSavePath, project_name)
            if os.path.isdir(project_path):
                project_a = []
                project_b = []
                project_c = []
                for file_name in os.listdir(project_path):
                    if file_name.endswith('.pickle'):
                        with open(os.path.join(project_path, file_name), 'rb') as f:
                            data = pickle.load(f)
                            if file_name == 'patternList.pickle':
                                project_a += data
                            elif file_name == 'posList.pickle':
                                project_b += data
                            elif file_name == 'constrainList.pickle':
                                project_c += data
                ta.extend(project_a)
                tb.extend(project_b)
                tc.extend(project_c)
    else:
        project_path = os.path.join(varSavePath, curProjectName)
        if os.path.isdir(project_path):
            project_a = []
            project_b = []
            project_c = []
            for file_name in os.listdir(project_path):
                if file_name.endswith('.pickle'):
                    with open(os.path.join(project_path, file_name), 'rb') as f:
                        data = pickle.load(f)
                        if file_name == 'patternList.pickle':
                            project_a += data
                        elif file_name == 'posList.pickle':
                            project_b += data
                        elif file_name == 'constrainList.pickle':
                            project_c += data
            ta.extend(project_a)
            tb.extend(project_b)
            tc.extend(project_c)
    return ta, tb, tc

import os
import pickle

def save_project(project_name, funcDefSumDict, nameListForReach, resRepGlobList, EHRRList, EHDataList, EHJumpList, funcSuspiciousDict, funcDefOrder, funcSuspiciousAccessDict, funcSuspiciousCallPathDict, globalContext):
    project_dir = os.path.join(projectSavePath, project_name)
    if not os.path.exists(project_dir):
        os.makedirs(project_dir)

    var_path = os.path.join(project_dir, "funcDefSumDict.pickle")
    with open(var_path, "wb") as f:
        pickle.dump(funcDefSumDict, f)

    var_path = os.path.join(project_dir, "nameListForReach.pickle")
    with open(var_path, "wb") as f:
        pickle.dump(nameListForReach, f)

    var_path = os.path.join(project_dir, "resRepGlobList.pickle")
    with open(var_path, "wb") as f:
        pickle.dump(resRepGlobList, f)

    var_path = os.path.join(project_dir, "EHRRList.pickle")
    with open(var_path, "wb") as f:
        pickle.dump(EHRRList, f)

    var_path = os.path.join(project_dir, "EHDataList.pickle")
    with open(var_path, "wb") as f:
        pickle.dump(EHDataList, f)

    var_path = os.path.join(project_dir, "EHJumpList.pickle")
    with open(var_path, "wb") as f:
        pickle.dump(EHJumpList, f)

    var_path = os.path.join(project_dir, "funcSuspiciousDict.pickle")
    with open(var_path, "wb") as f:
        pickle.dump(funcSuspiciousDict, f)

    var_path = os.path.join(project_dir, "funcDefOrder.pickle")
    with open(var_path, "wb") as f:
        pickle.dump(funcDefOrder, f)

    var_path = os.path.join(project_dir, "funcSuspiciousAccessDict.pickle")
    with open(var_path, "wb") as f:
        pickle.dump(funcSuspiciousAccessDict, f)

    var_path = os.path.join(project_dir, "funcSuspiciousCallPathDict.pickle")
    with open(var_path, "wb") as f:
        pickle.dump(funcSuspiciousCallPathDict, f)

    var_path = os.path.join(project_dir, "globalContext.pickle")
    with open(var_path, "wb") as f:
        pickle.dump(globalContext, f)

def load_variables(project_name):

    project_dir = os.path.join(projectSavePath, project_name)

    variables = {}
    for file in os.listdir(project_dir):
        if file.endswith(".pickle"):
            var_name = file.split(".")[0]
            var_path = os.path.join(project_dir, file)
            with open(var_path, "rb") as f:
                var_data = pickle.load(f)
            variables[var_name] = var_data
    return variables
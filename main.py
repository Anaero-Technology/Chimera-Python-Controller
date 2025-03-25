import tkinter
import tkinter.ttk as Ttk
from tkinter.ttk import Style
from tkinter import messagebox, simpledialog, filedialog, font
import serial
from matplotlib.figure import Figure 
from matplotlib.backends.backend_tkagg import (FigureCanvasTkAgg)
from serial.tools import list_ports
from threading import Thread
import datetime
import numpy
import math
import os, pathlib, sys
import notifypy
from PIL import Image, ImageTk
import time

class MainWindow(tkinter.Frame):
    '''Class to contain all of the menus'''
    def __init__(self, parent, *args, **kwargs) -> None:
        #Setup parent configuration
        tkinter.Frame.__init__(self, parent, *args, **kwargs)
        self.parent = parent
        self.grid_rowconfigure(0, weight=1)
        self.grid_columnconfigure(0, weight=1)

        #Text colours
        self.blackTextColour = "#000000"
        self.blueTextColour = "#3333FF"
        self.greenTextColour = "#229922"
        self.redTextColour = "#FF3333"

        #Fonts
        self.fonts = {"huge":("", 22), "large":("", 18), "medium":("", 14), "small":("",10), "small-bold":("", 10, "bold")}

        #Icons loaded from files
        self.gearIcon = tkinter.PhotoImage(file=self.pathTo("images/settingsIcon.png"))
        self.fileIcon = tkinter.PhotoImage(file=self.pathTo("images/filePresent.png"))
        self.crossIcon = tkinter.PhotoImage(file=self.pathTo("images/cross.png"))
        self.smallCrossIcon = tkinter.PhotoImage(file=self.pathTo("images/smallCross.png"))
        self.tickIcon = tkinter.PhotoImage(file=self.pathTo("images/tick.png"))

        #Setup colours to use for different ui elements
        self.defaultColour = self.cget("bg")
        self.selectedColour = "#AADDAA"
        self.methaneColour = "#7799FF"
        self.carbonColour = "#FF7777"
        self.darkenedColour = "#777777"

        self.lastEvent = time.time()
        self.currentValve = -1

        #Current open and flush duration
        self.currentOpen = 0
        self.currentFlush = 0

        #Which type of window is currently being used
        self.methaneOpen = False
        self.carbonDioxideOpen = False

        #The message that is being read
        self.currentMessage = ""
        #A list of messages that were previously read but not processed yet
        self.receivedMessages = []
        #If waiting for a response from the esp32 (possibly add a timeout)
        self.awaiting = False
        self.downloading = False
        self.awaitingFiles = False

        self.percentageValue = 0
        #Percentage values entered from known gas concentrations
        self.ch4Percentages = []
        self.co2Percentages = []
        #Used for calibration point values
        self.ch4Values = []
        self.co2Values = []
        #Results from regression of points
        self.ch4Regression = []
        self.co2Regression = []
        #Points to be displayed on calibration graphs
        self.co2PlotPoints = [[], []]
        self.ch4PlotPoints = [[], []]

        #Extra data points to show peak of sensor readings and 4 before
        self.ch4DebugData = [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
        self.co2DebugData = [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

        #List of accepted characters for file names as a string
        self.acceptedChars = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijlkmnopqrstuvwxyz-_"

        #Name of file being saved to
        self.fileNameToSave = ""
        #Information being saved to the file
        self.fileDataToSave = ""

        #If still waiting for first response
        self.awaitingCommunication = False
        #Timeout timers
        self.timesTried = 0
        self.timeoutAttempts = 10

        #Valid file save types
        self.fileTypes = [("CSV Files", "*.csv")]

        #Values to store for the progress of a download
        self.downloadedCharacters = 0
        self.charactersToDownload = 0

        #Line position in current file
        self.currentLine = 0

        #Calibration values currently in gas sensor - and if they have been updated recently
        self.storedCalibration = [[0.0, 0.0, 0.0, 0.0], [0.0, 0.0, 0.0, 0.0]]
        self.calibrationUpdated = False

        #Information about each valve being opened or closed
        self.valveStates = [False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False]
        #Which channels are currently in service
        self.currentService = [True, True, True, True, True, True, True, True, True, True, True, True, True, True, True]

        #If the device is currently connected
        self.connected = False
        #Current connected port name
        self.connectedPort = ""
        #Index of currently selected file
        self.selectedFile = -1

        #Object to hold serial connection to port
        self.serialConnection = None
        #Whether or not the device is in calibration mode
        self.calibrating = False

        #List of available port names
        self.portLabels = []

        #List of available files (for testing)
        self.files = ["File Number 1", "File Number 2"]
        self.fileSizes = []

        #Current working file on esp
        self.currentFileName = ""
        #Current file based on device time
        self.currentTimeFileName = ""

        self.ch4AddType = "auto"
        self.co2AddType = "auto"
        self.ch4AddPercent = -1
        self.co2AddPercent = -1
        self.ch4AddValue = -1
        self.co2AddValue = -1

        self.calibratingMethane = True
        self.calibrationActionTime = 0
        self.calibrationReadTime = 30
        self.calibrationFlushTime = 15
        self.calibrationReading = True
        self.calibrationFlushing = False
        self.calibratingPoint = False

        """Connection Frame"""
        self.connectFrame = tkinter.Frame(self)
        #Frame to keep all elements in the center
        self.connectButtonsFrame = tkinter.Frame(self.connectFrame)
        self.connectButtonsFrame.pack(expand=True)
        #Text label to prompt user
        self.connectInfoLabel = tkinter.Label(self.connectButtonsFrame, text="Select port to connect to Chimera", font=self.fonts["huge"])
        self.connectInfoLabel.pack(side="top", anchor="center", pady=20)
        #Frame to hold buttons horizonally centered
        self.connectInternalFrame = tkinter.Frame(self.connectButtonsFrame)
        self.connectInternalFrame.pack(side="top", anchor="center")
        #Setup port drop down (with debug values)
        self.selectedPort = tkinter.StringVar()
        self.selectedPort.set("Port 1")
        self.portOption = tkinter.OptionMenu(self.connectInternalFrame, self.selectedPort, "Port 1", "Port 2", "Port 3", "Port 4")
        self.parent.nametowidget(self.portOption.menuname).configure(font=self.fonts["large"])
        self.portOption.configure(font=self.fonts["large"])
        self.portOption.pack(side="left", anchor="center", fill="x", padx=10)
        #Add connect button
        self.connectButton = tkinter.Button(self.connectInternalFrame, text="Connect", command=self.connectPressed, font=self.fonts["large"])
        self.connectButton.pack(side="left", anchor="center", fill="x", padx=10)
        #Button colours
        self.defaultButtonColour = self.connectButton.cget("bg")
        self.selectedButtonColour = "#70D070"

        """View Frame"""
        self.viewFrame = tkinter.Frame(self)
        #Setup view frame grid
        for row in range(0, 7):
            self.viewFrame.grid_rowconfigure(row, weight=1)
        for col in range(0, 8):
            self.viewFrame.grid_columnconfigure(col, weight=1)
        #List of objects representing each display area for channel results
        self.percentageViews = []
        #Iterate all channels
        for i in range(0, 16):
            #The frame to hold everything
            display = {"frame" : tkinter.Frame(self.viewFrame, highlightbackground="black", highlightthickness=1)}
            display["frame"].grid_rowconfigure(0, weight=1)
            display["frame"].grid_rowconfigure(1, weight=1)
            display["frame"].grid_rowconfigure(2, weight=10)
            display["frame"].grid_rowconfigure(3, weight=1)
            display["frame"].grid_columnconfigure(0, weight=1)
            display["frame"].grid_columnconfigure(1, weight=1)
            #Title text label
            reactorName = "Reactor {0}".format(i + 1)
            if i == 15:
                reactorName = "Flush"
            display["label"] = tkinter.Label(display["frame"], text=reactorName, font=self.fonts["small-bold"])
            display["label"].grid(row=0, column=0, columnspan=2, sticky="NESW")

            #Methane text percentage and link to graph
            display["ch4Text"] = tkinter.Label(display["frame"], text="75%")
            display["ch4Text"].grid(row=1, column=0, padx=1, sticky="NESW")
            display["ch4Text"].bind("<Button-1>", lambda event,x=i:self.methanePointsPressed(x))
            #Frame to hold bar
            display["ch4Out"] = tkinter.Frame(display["frame"])
            display["ch4Out"].grid(row=2, column=0, padx=1, sticky="NESW")
            #Methane bar
            display["ch4Bar"] = tkinter.Frame(display["ch4Out"])
            display["ch4Bar"].place(rely=0.25, relheight=0.75, relwidth=1.0)
            #Button within bar for apprearance
            display["ch4ViewButton"] = tkinter.Button(display["ch4Bar"], command=lambda x=i:self.methanePointsPressed(x), bg=self.methaneColour)
            display["ch4ViewButton"].pack(expand=True, fill="both")
            #Label text for methane
            display["ch4"] = tkinter.Label(display["frame"], text="CH4")
            display["ch4"].grid(row=3, column=0, padx=1, sticky="NESW")

            #Carbon dioxide text percentage and link to graph
            display["co2Text"] = tkinter.Label(display["frame"], text="25%")
            display["co2Text"].grid(row=1, column=1, padx=1, sticky="NESW")
            display["co2Text"].bind("<Button-1>", lambda event,x=i:self.carbonPointsPressed(x))
            #Frame to hold bar
            display["co2Out"] = tkinter.Frame(display["frame"])
            display["co2Out"].grid(row=2, column=1, padx=1, sticky="NESW")
            #Carbon dioxide bar
            display["co2Bar"] = tkinter.Frame(display["co2Out"])
            display["co2Bar"].place(rely=0.75, relheight=0.25, relwidth=1.0)
            #Button within bar for appearance
            display["co2ViewButton"] = tkinter.Button(display["co2Bar"], command=lambda x=i:self.carbonPointsPressed(x), bg=self.carbonColour)
            display["co2ViewButton"].pack(expand=True, fill="both")
            #Label text for carbon dioxide
            display["co2"] = tkinter.Label(display["frame"], text="CO2")
            display["co2"].grid(row=3, column=1, padx=1, sticky="NESW")
            #Add to list of objects
            self.percentageViews.append(display)
            #Find correct position and place on screen
            r = i // 8
            c = i - (r * 8)
            display["frame"].grid(row=r * 2, column=c, rowspan=2, sticky="NESW")
        #Frame to hold information about event timing
        self.timingViewFrame = tkinter.Frame(self.viewFrame)
        self.timingViewFrame.grid(row=4, column=0, columnspan=8, sticky="NESW")
        #Internal frame to hold widgets centered
        self.timingInternalFrame = tkinter.Frame(self.timingViewFrame)
        self.timingInternalFrame.pack(expand=True)
        #Label to display time open
        self.openTimeLabel = tkinter.Label(self.timingInternalFrame, text="Open Time: {0}s".format(self.currentOpen), font=self.fonts["medium"])
        self.openTimeLabel.pack(anchor="center", side="left", padx=10, fill="x")
        self.flushTimeLabel = tkinter.Label(self.timingInternalFrame, text="Flush Time: {0}s".format(self.currentFlush), font=self.fonts["medium"])
        self.flushTimeLabel.pack(anchor="center", side="left", padx=10, fill="x")
        self.currentTimeInfoButton = tkinter.Button(self.timingInternalFrame, text="Currently Waiting", font=self.fonts["medium"], command=self.openValveWindow)
        self.currentTimeInfoButton.pack(anchor="center", side="left", padx=10, fill="x")
        #Frame to hold buttons to access other windows
        self.viewOptionsButtonsFrame = tkinter.Frame(self.viewFrame)
        self.viewOptionsButtonsFrame.grid(row=5, column=0, rowspan=2, columnspan=8, sticky="NESW")
        self.viewOptionsButtonsFrame.grid_rowconfigure(0, weight=1)
        self.viewOptionsButtonsFrame.grid_columnconfigure(0, weight=1)
        self.viewOptionsButtonsFrame.grid_columnconfigure(1, weight=1)
        #Add configure button
        self.configureButton = tkinter.Button(self.viewOptionsButtonsFrame, text="Configure Chimera", image=self.gearIcon, compound="top", command=self.configurePressed, font=self.fonts["medium"])
        self.configureButton.grid(row=0, column=0)
        #Add files button
        self.fileViewButton = tkinter.Button(self.viewOptionsButtonsFrame, text="View Files", image=self.fileIcon, compound="top", command=self.viewFilesPressed, font=self.fonts["medium"])
        self.fileViewButton.grid(row=0, column=1)

        """Graph Window""" #Window to display graphs of the peak values from the sensor
        self.graphWindow = tkinter.Toplevel(self)
        self.graphWindow.title("Sensor Reading Overview")
        self.graphWindow.geometry("450x400")
        self.graphWindow.minsize(450, 400)
        self.graphWindow.protocol("WM_DELETE_WINDOW", self.closeGraph)
        self.graphWindow.grid_rowconfigure(0, weight=1)
        self.graphWindow.grid_rowconfigure(1, weight=10)
        self.graphWindow.grid_columnconfigure(0, weight=1)
        #Label to show title
        self.graphWindowHeaderLabel = tkinter.Label(self.graphWindow, text="Channel - Data Points", font=self.fonts["medium"])
        self.graphWindowHeaderLabel.grid(row=0, column=0, columnspan=2, sticky="NESW")
        #Plot for the points to be displayed
        self.debugFigure = Figure(figsize=(5, 5), dpi=100)
        self.debugPlot = self.debugFigure.add_subplot(111)
        self.debugPlot.set_title("Methane")
        self.debugCanvas = FigureCanvasTkAgg(self.debugFigure, master=self.graphWindow)
        self.debugCanvas.get_tk_widget().grid(row=1, column=0)
        #Widthdraw the window
        self.closeGraph()

        """Valve Window""" #Window to display which valves are open right now
        #The valve window is not currently visible
        self.valveWindowOpen = False
        self.valveWindow = tkinter.Toplevel(self)
        self.valveWindow.title("Valve Display")
        self.valveWindow.protocol("WM_DELETE_WINDOW", self.closeValveWindow)
        self.valveWindow.geometry("300x300")
        self.valveWindow.resizable(False, False)
        #Canvas to hold drawing
        self.valveCanvas = tkinter.Canvas(self.valveWindow, height=300, width=300)
        self.valveCanvas.grid(row=0, column=0, sticky="NESW")
        #Widthdraw window
        self.closeValveWindow()

        """Configure Frame"""
        self.configureFrame = tkinter.Frame(self)
        #Calculate default colour as matplotlib colour, convert to 0-1 range by dividing by 65535 (16 bit maximum)
        self.graphBackground = list(self.winfo_rgb(self.defaultButtonColour))
        for i in range(0, len(self.graphBackground)):
            self.graphBackground[i] = self.graphBackground[i] / 65535
        #Graph to show methane calibration points
        self.calibrationFigureCh4 = Figure(figsize=(5, 5), dpi=100)
        self.calibrationFigureCh4.set_size_inches(3.5, 2)
        self.ch4CalPlot = self.calibrationFigureCh4.add_subplot(111)
        self.ch4CalPlot.set_title("Methane Calibration")
        self.ch4CalPlot.set_xlim(0, 100)
        self.ch4CalPlot.set_ylim(1000, 2000)
        self.ch4CalPlot.set_facecolor(self.graphBackground)
        self.calibrationFigureCh4.set_facecolor(self.graphBackground)
        #Graph to show carbon dioxide calibration points
        self.calibrationFigureCo2 = Figure(figsize=(5, 5), dpi=100)
        self.calibrationFigureCo2.set_size_inches(3.5, 2)
        self.co2CalPlot = self.calibrationFigureCo2.add_subplot(111)
        self.co2CalPlot.set_title("Carbon Dioxide Calibration")
        self.co2CalPlot.set_xlim(0, 100)
        self.co2CalPlot.set_ylim(1000, 2000)
        self.co2CalPlot.set_facecolor(self.graphBackground)
        self.calibrationFigureCo2.set_facecolor(self.graphBackground)
        #Grid setup
        for row in range(0, 9):
            self.configureFrame.grid_rowconfigure(row, weight=1)
        for col in range(0, 4):
            self.configureFrame.grid_columnconfigure(col, weight=1)
        #Label to mark methane section
        self.ch4ConfigLabel = tkinter.Label(self.configureFrame, text="Methane", font=self.fonts["large"])
        self.ch4ConfigLabel.grid(row=0, column=0, columnspan=2, sticky="NESW")
        #Canvases to hold graphs for calibrations
        self.ch4CalCanvas = FigureCanvasTkAgg(self.calibrationFigureCh4, master=self.configureFrame)
        self.ch4CalCanvas.get_tk_widget().grid(row=1, column=0, columnspan=2)
        
        self.setupValueCh4TimingFrame = tkinter.Frame(self.configureFrame)
        self.setupValueCh4TimingFrame.grid(row=3, column=0, columnspan=2, pady=5, sticky="NESW")
        self.setupValueCh4TimingLabel = tkinter.Label(self.setupValueCh4TimingFrame, text="Valve 1 open, reading. 60s remaining.", font=self.fonts["medium"], anchor="center", justify="center")
        self.setupValueCh4TimingLabel.pack(anchor="center", fill="x", padx=5)
        self.setupValueEntryCh4PointFrame = tkinter.Frame(self.configureFrame)
        self.setupValueEntryCh4PointFrame.grid(row=3, column=0, columnspan=2, pady=5, sticky="NESW")
        self.setupValueCh4InternalFrame = tkinter.Frame(self.setupValueEntryCh4PointFrame)
        self.setupValueCh4InternalFrame.pack(side="top", anchor="center")
        self.setupValueEntryCh4PointLabel = tkinter.Label(self.setupValueCh4InternalFrame, text="Percent:", font=self.fonts["medium"])
        self.setupValueEntryCh4PointLabel.pack(side="left", anchor="center", fill="x")
        self.setupValueEntryCh4PointEntry = tkinter.Entry(self.setupValueCh4InternalFrame, width=5, font=self.fonts["medium"])
        self.setupValueEntryCh4PointEntry.pack(side="left", anchor="center", fill="x")
        self.setupValueEntryCh4PointAcceptButton = tkinter.Button(self.setupValueCh4InternalFrame, image=self.tickIcon, command=lambda:self.valueAddConfirmPressed(True))
        self.setupValueEntryCh4PointAcceptButton.pack(side="left", anchor="center", fill="x", padx=5)
        self.setupValueEntryCh4PointCancelButton = tkinter.Button(self.setupValueCh4InternalFrame, image=self.crossIcon, command=lambda:self.cancelPointPressed(True))
        self.setupValueEntryCh4PointCancelButton.pack(side="left", anchor="center", fill="x", padx=5)
        self.setupCh4PointFrame = tkinter.Frame(self.configureFrame)
        self.setupCh4PointFrame.grid(row=3, column=0, columnspan=2, pady=5, sticky="NESW")
        self.setupCh4PointFrame.grid_rowconfigure(0, weight=1)
        self.setupCh4PointFrame.grid_columnconfigure(0, weight=1)
        self.setupCh4PointFrame.grid_columnconfigure(1, weight=1)
        self.setupCh4PointFrame.grid_columnconfigure(2, weight=1)
        self.automaticCh4PointButton = tkinter.Button(self.setupCh4PointFrame, text="Use Sensor Value", command=lambda:self.automaticPressed(True), font=self.fonts["medium"])
        self.automaticCh4PointButton.grid(row=0, column=0)
        self.manualCh4PointButton = tkinter.Button(self.setupCh4PointFrame, text="Manual Entry", command=lambda:self.manualPressed(True), font=self.fonts["medium"])
        self.manualCh4PointButton.grid(row=0, column=1)
        self.cancelCh4PointButton = tkinter.Button(self.setupCh4PointFrame, image=self.crossIcon, font=self.fonts["medium"], command=lambda:self.cancelPointPressed(True))
        self.cancelCh4PointButton.grid(row=0, column=2)
        self.addCh4PointButtonFrame = tkinter.Frame(self.configureFrame)
        self.addCh4PointButtonFrame.grid(row=3, column=0, columnspan=2, pady=5, sticky="NESW")
        #Buttons to allow for points to be added to calibration curves
        self.addPointCh4Button = tkinter.Button(self.addCh4PointButtonFrame, text="+ Add Point", command=lambda:self.addPointPressed(True), font=self.fonts["medium"])
        self.addPointCh4Button.pack()

        self.setupValueEntryCh4PointEntry.bind("<Return>", lambda entry:self.valueAddConfirmPressed(True))

        self.calculateCh4Frame = tkinter.Frame(self.configureFrame)
        self.calculateCh4Frame.grid(row=4, column=0, columnspan=2, sticky="NESW")
        #Buttons to allow for calibration values to be sent to the device
        self.calculateCh4Button = tkinter.Button(self.calculateCh4Frame, text="Configure Calibration", command=lambda:self.openCalculation(True), font=self.fonts["medium"])
        self.calculateCh4Button.pack()

        #Label to mark carbon dioxide section
        self.co2ConfigLabel = tkinter.Label(self.configureFrame, text="Carbon Dioxide", font=self.fonts["large"])
        self.co2ConfigLabel.grid(row=5, column=0, columnspan=2, sticky="NESW")
        self.co2CalCanvas = FigureCanvasTkAgg(self.calibrationFigureCo2, master=self.configureFrame)
        self.co2CalCanvas.get_tk_widget().grid(row=6, column=0, columnspan=2)
        self.setupValueCo2TimingFrame = tkinter.Frame(self.configureFrame)
        self.setupValueCo2TimingFrame.grid(row=7, column=0, columnspan=2, pady=5, sticky="NESW")
        self.setupValueCo2TimingLabel = tkinter.Label(self.setupValueCo2TimingFrame, text="Valve 1 open, reading. 60s remaining.", font=self.fonts["medium"], anchor="center", justify="center")
        self.setupValueCo2TimingLabel.pack(anchor="center", fill="x", padx=5)
        self.setupValueEntryCo2PointFrame = tkinter.Frame(self.configureFrame)
        self.setupValueEntryCo2PointFrame.grid(row=7, column=0, columnspan=2, pady=5, sticky="NESW")
        self.setupValueCo2InternalFrame = tkinter.Frame(self.setupValueEntryCo2PointFrame)
        self.setupValueCo2InternalFrame.pack(side="top", anchor="center")
        self.setupValueEntryCo2PointLabel = tkinter.Label(self.setupValueCo2InternalFrame, text="Percent:", font=self.fonts["medium"])
        self.setupValueEntryCo2PointLabel.pack(side="left", anchor="center", fill="x")
        self.setupValueEntryCo2PointEntry = tkinter.Entry(self.setupValueCo2InternalFrame, width=5, font=self.fonts["medium"])
        self.setupValueEntryCo2PointEntry.pack(side="left", anchor="center", fill="x")
        self.setupValueEntryCo2PointAcceptButton = tkinter.Button(self.setupValueCo2InternalFrame, image=self.tickIcon, command=lambda:self.valueAddConfirmPressed(False))
        self.setupValueEntryCo2PointAcceptButton.pack(side="left", anchor="center", fill="x", padx=5)
        self.setupValueEntryCo2PointCancelButton = tkinter.Button(self.setupValueCo2InternalFrame, image=self.crossIcon, command=lambda:self.cancelPointPressed(False))
        self.setupValueEntryCo2PointCancelButton.pack(side="left", anchor="center", fill="x", padx=5)
        self.setupCo2PointFrame = tkinter.Frame(self.configureFrame)
        self.setupCo2PointFrame.grid(row=7, column=0, columnspan=2, pady=5, sticky="NESW")
        self.setupCo2PointFrame.grid_rowconfigure(0, weight=1)
        self.setupCo2PointFrame.grid_columnconfigure(0, weight=1)
        self.setupCo2PointFrame.grid_columnconfigure(1, weight=1)
        self.setupCo2PointFrame.grid_columnconfigure(2, weight=1)
        self.automaticCo2PointButton = tkinter.Button(self.setupCo2PointFrame, text="Use Sensor Value", command=lambda:self.automaticPressed(False), font=self.fonts["medium"])
        self.automaticCo2PointButton.grid(row=0, column=0)
        self.manualCo2PointButton = tkinter.Button(self.setupCo2PointFrame, text="Manual Entry", command=lambda:self.manualPressed(False), font=self.fonts["medium"])
        self.manualCo2PointButton.grid(row=0, column=1)
        self.cancelCo2PointButton = tkinter.Button(self.setupCo2PointFrame, image=self.crossIcon, font=self.fonts["medium"], command=lambda:self.cancelPointPressed(False))
        self.cancelCo2PointButton.grid(row=0, column=2)
        self.addCo2PointButtonFrame = tkinter.Frame(self.configureFrame)
        self.addCo2PointButtonFrame.grid(row=7, column=0, columnspan=2, pady=5, sticky="NESW")
        #Buttons to allow for points to be added to calibration curves
        self.addPointCo2Button = tkinter.Button(self.addCo2PointButtonFrame, text="+ Add Point", command=lambda:self.addPointPressed(False), font=self.fonts["medium"])
        self.addPointCo2Button.pack()

        self.setupValueEntryCo2PointEntry.bind("<Return>", lambda entry:self.valueAddConfirmPressed(False))

        self.calculateCo2Frame = tkinter.Frame(self.configureFrame)
        self.calculateCo2Frame.grid(row=8, column=0, columnspan=2, sticky="NESW")
        self.calculateCo2Button = tkinter.Button(self.calculateCo2Frame, text="Configure Calibration", command=lambda:self.openCalculation(False), font=self.fonts["medium"])
        self.calculateCo2Button.pack()

        #Label to act as header for channel service configuration section
        self.enabledValvesLabel = tkinter.Label(self.configureFrame, text="Channels In Service", font=self.fonts["large"])
        self.enabledValvesLabel.grid(row=0, column=2, columnspan=2, sticky="NESW")
        #Frame to hold buttons and labels for in service
        self.enabledValvesFrame = tkinter.Frame(self.configureFrame)
        self.enabledValvesFrame.grid(row=1, column=2, columnspan=2, rowspan=2, sticky="NESW")
        for row in range(0, 6):
            self.enabledValvesFrame.grid_rowconfigure(row, weight=1)
        for col in range(0, 5):
            self.enabledValvesFrame.grid_columnconfigure(col, weight=1)
        #List to hold buttons so they can be reconfigured later
        self.enabledButtons = []
        currentColumn = 0
        currentRow = 1
        for i in range(0, 15):
            #Create label and button with link to callback for the toggle being pressed
            label = tkinter.Label(self.enabledValvesFrame, text="{0}".format(i + 1), font=self.fonts["small-bold"])
            label.grid(row=currentRow - 1, column=currentColumn)
            button = tkinter.Button(self.enabledValvesFrame, text="Enabled", bg=self.selectedButtonColour, command=lambda x=i : self.toggleServicePressed(x), font=self.fonts["small"])
            button.grid(row=currentRow, column=currentColumn)
            #Increment positioning
            currentColumn = currentColumn + 1
            if currentColumn > 4:
                currentColumn = 0
                currentRow = currentRow + 2
            self.enabledButtons.append(button)
        #Frame to hold all the timing information
        self.timingsFrame = tkinter.Frame(self.configureFrame)
        self.timingsFrame.grid(row=4, column=2, columnspan=2, rowspan=4,)
        #Heading text
        self.timingsLabel = tkinter.Label(self.timingsFrame, text="Timings", font=self.fonts["large"])
        self.timingsLabel.pack(pady=3)
        #Frames to hold the open and flush time parts centered
        self.timingOpenInputFrame = tkinter.Frame(self.timingsFrame)
        self.timingOpenInputFrame.pack(pady=3)
        self.timingFlushInputFrame = tkinter.Frame(self.timingsFrame)
        self.timingFlushInputFrame.pack(pady=3)
        #Label and entry for open and flush time
        self.openTimingLabel = tkinter.Label(self.timingOpenInputFrame, text="Open Time:", font=self.fonts["medium"])
        self.openTimeEntry = tkinter.Entry(self.timingOpenInputFrame, font=self.fonts["medium"], width=5, justify="center")
        self.flushTimeingLabel = tkinter.Label(self.timingFlushInputFrame, text="Flush Time:", font=self.fonts["medium"])
        self.flushTimeEntry = tkinter.Entry(self.timingFlushInputFrame, font=self.fonts["medium"], width=5, justify="center")
        self.openTimingLabel.pack(side="left", anchor="center", fill="x", pady=3)
        self.openTimeEntry.pack(side="left", anchor="center", fill="x", pady=3)
        self.flushTimeingLabel.pack(side="left", anchor="center", fill="x", pady=3)
        self.flushTimeEntry.pack(side="left", anchor="center", fill="x", pady=3)
        #Button to send the timings to the device
        self.updateTimingsButton = tkinter.Button(self.timingsFrame, text="Update Timings", command=self.updateTimingPressed, font=self.fonts["medium"])
        self.updateTimingsButton.pack(pady=3)
        #Label to display the current internal clock time of the device
        self.currentClockTimeLabel = tkinter.Label(self.configureFrame, text="Current: 00:00:00 01/01/1970", relief="sunken", font=self.fonts["medium"])
        self.currentClockTimeLabel.grid(row=8, column=2, pady=15)
        #Button to request that the time be sent from the computer to the device
        self.timeButton = tkinter.Button(self.configureFrame, text="Update Current Time", command=self.setTimePressed, font=self.fonts["medium"])
        self.timeButton.grid(row=8, column=3, pady=15)
        #Button to close the configuration screen and return to the main window
        self.endConfigureButton = tkinter.Button(self.configureFrame, text="Close Configuration", font=self.fonts["large"], command=self.endConfigurePressed)
        self.endConfigureButton.grid(row=9, column=2, columnspan=2, rowspan=2, pady=15)

        """Calculations Window""" #New window to display point calculations and allow for calibration entry
        self.calculationsWindow = tkinter.Toplevel(self)
        self.calculationsWindow.title("Calibration Calculations")
        self.calculationsWindow.protocol("WM_DELETE_WINDOW", self.closeCalculations)
        for r in range(0, 15):
            self.calculationsWindow.grid_rowconfigure(r, weight=1)
        for c in range(0, 7):
            self.calculationsWindow.grid_columnconfigure(c, weight=1)
        #Heading text
        self.calculationsWindowHeader = tkinter.Label(self.calculationsWindow, text="Methane Calculations", font=self.fonts["medium"])
        self.calculationsWindowHeader.grid(row=0, column=0, columnspan=9, sticky="NESW")
        #String variables to store current text in calibration entries
        self.calValues = [tkinter.StringVar(), tkinter.StringVar(), tkinter.StringVar(), tkinter.StringVar()]
        #Entries to display calibration values
        self.entryThree = tkinter.Entry(self.calculationsWindow, font=self.fonts["small"], textvariable=self.calValues[3], width=9, justify="right")
        self.entryThree.grid(row=1, column=0, sticky="NESW")
        self.entryTwo = tkinter.Entry(self.calculationsWindow, font=self.fonts["small"], textvariable=self.calValues[2], width=9, justify="right")
        self.entryTwo.grid(row=1, column=2, sticky="NESW")
        self.entryOne = tkinter.Entry(self.calculationsWindow, font=self.fonts["small"], textvariable=self.calValues[1], width=9, justify="right")
        self.entryOne.grid(row=1, column=4, sticky="NESW")
        self.entryZero = tkinter.Entry(self.calculationsWindow, font=self.fonts["small"], textvariable=self.calValues[0], width=9, justify="right")
        self.entryZero.grid(row=1, column=6, sticky="NESW")
        #Labels to display mathematical usage of values as part of a polynomial
        self.labelThree = tkinter.Label(self.calculationsWindow, font=self.fonts["small"], text="x^3 +")
        self.labelThree.grid(row=1, column=1, sticky="NESW")
        self.labelTwo = tkinter.Label(self.calculationsWindow, font=self.fonts["small"], text="x^2 +")
        self.labelTwo.grid(row=1, column=3, sticky="NESW")
        self.labelOne = tkinter.Label(self.calculationsWindow, font=self.fonts["small"], text="x +")
        self.labelOne.grid(row=1, column=5, sticky="NESW")
        #List of labels used to display calibration points once they have been captured
        self.tempLabels = []
        #Button to send the polynomal calibration to the gas sensor
        self.sendCalculationButton = tkinter.Button(self.calculationsWindow, text="Update Calibration", command=self.sendCalculationPressed)
        self.sendCalculationButton.grid(row=2, column=1, columnspan=5, sticky="NESW")
        #Widthdraw the window
        self.closeCalculations()

        """Files Frame"""
        self.filesFrame = tkinter.Frame(self)
        #Setup parts for the scrolling canvas
        self.fileCanvas = None
        self.fileScroll = None
        self.fileGridFrame = None
        self.fileButtons = []
        self.fileCanvasWindow = None
        for row in range(0, 8):
            self.filesFrame.grid_rowconfigure(row, weight=1)
        for col in range(0, 10):
            self.filesFrame.grid_columnconfigure(col, weight=1)
        #Default string and label to display sd card capacity
        self.sdCardString = "SD Card: {0}/{1}MB {2}% Used"
        self.sdCardInfoLabel = tkinter.Label(self.filesFrame, text="SD Card: 0/0MB 0% Used", font=self.fonts["medium"])
        self.sdCardInfoLabel.grid(row=0, column=0, columnspan=10, sticky="NESW")
        #Add a frame to put the list of files into
        self.fileListFrame = tkinter.Frame(self.filesFrame, bg="#FFFFFF")
        self.fileListFrame.grid(row=1, column=0, columnspan=10, rowspan=7, sticky="NESW")
        #Add button to open separator settings
        self.separatorButton = tkinter.Button(self.filesFrame, image=self.gearIcon, command=self.openSeparators)
        self.separatorButton.grid(row=8, column=0)
        #Add label for selected file name
        self.fileLabel = tkinter.Label(self.filesFrame, text="No file selected", font=self.fonts["medium"])
        self.fileLabel.grid(row=8, column=1, columnspan=3, sticky="NESW")
        #Add download file button
        self.downloadFileButton = tkinter.Button(self.filesFrame, text="Download", state="disabled", command=self.downloadPressed, font=self.fonts["medium"])
        self.downloadFileButton.grid(row=8, column=4, columnspan=2, sticky="NESW")
        #Add delete file button
        self.deleteFileButton = tkinter.Button(self.filesFrame, text="Delete", state="disabled", command=self.deletePressed, font=self.fonts["medium"])
        self.deleteFileButton.grid(row=8, column=6, columnspan=2, sticky="NESW")
        #Add button to return to the main view
        self.closeFileButton = tkinter.Button(self.filesFrame, text="Close Files", command=self.closeFileView, font=self.fonts["medium"])
        self.closeFileButton.grid(row=8, column=8, columnspan=2, sticky="NESW")
        #Get the style object for the parent window
        self.styles = Style(self.parent)
        #Create layout for progress bar with a label
        self.styles.layout("ProgressbarLabeled", [("ProgressbarLabeled.trough", {"children": [("ProgressbarLabeled.pbar", {"side": "left", "sticky": "NS"}), ("ProgressbarLabeled.label", {"sticky": ""})], "sticky": "NESW"})])
        #Set the bar colour of the progress bar
        self.styles.configure("ProgressbarLabeled", background="lightgreen")
        #Create a progress bar
        self.progressBar = Ttk.Progressbar(self.filesFrame, orient="horizontal", mode="determinate", maximum=100.0, style="ProgressbarLabeled")
        #Set the text
        self.styles.configure("ProgressbarLabeled", text = "Downloading...00%")
        self.progressBar.grid(row=9, column=0, columnspan=10, sticky="NESW")
        self.progressBar.grid_remove()

        """Separator Window""" #Window to allow user to choose separators
        #Using comma separation
        self.comma = True
        #Load the separators from the memory file
        self.loadSeparators()
        self.separatorWindow = tkinter.Toplevel(self)
        self.separatorWindow.title("File Config")
        self.separatorWindow.protocol("WM_DELETE_WINDOW", self.closeSeparators)
        self.separatorWindow.geometry("400x200")
        self.separatorWindow.resizable(False, False)
        self.separatorWindow.grid_rowconfigure(0, weight=1)
        self.separatorWindow.grid_columnconfigure(0, weight=1)
        self.separatorWindow.grid_columnconfigure(1, weight=1)
        #Frame to hold comma option
        self.commaFrame = tkinter.Frame(self.separatorWindow)
        self.commaFrame.grid(row=0, column=0, sticky="NESW")
        self.commaFrame.grid_columnconfigure(0, weight=1)
        self.commaFrame.grid_rowconfigure(0, weight=1)
        self.commaFrame.grid_rowconfigure(1, weight=1)
        self.commaFrame.grid_rowconfigure(2, weight=1)
        #Frame to hold semicolon option
        self.semiFrame = tkinter.Frame(self.separatorWindow)
        self.semiFrame.grid(row=0, column=1, sticky="NESW")
        self.semiFrame.grid_columnconfigure(0, weight=1)
        self.semiFrame.grid_rowconfigure(0, weight=1)
        self.semiFrame.grid_rowconfigure(1, weight=1)
        self.semiFrame.grid_rowconfigure(2, weight=1)
        #Font to use for the header text
        self.headerFont = font.Font(size=14)
        #Title of the comma section
        self.commaTitle = tkinter.Label(self.commaFrame, text="Comma Separated", font=self.headerFont)
        self.commaTitle.grid(row=0, column=0, sticky="NESW")
        #Text for the comma section
        self.commaText = tkinter.Label(self.commaFrame, text="Column : ,  Decimal : .")
        self.commaText.grid(row=1, column=0, sticky="NESW")
        #Button to select comma
        self.commaButton = tkinter.Button(self.commaFrame, text="Choose", command=lambda x = True:self.changeSeparators(x))
        self.commaButton.grid(row=2, column=0)
        #Title for the semicolon section
        self.semiTitle = tkinter.Label(self.semiFrame, text="Semicolon Separated", font=self.headerFont)
        self.semiTitle.grid(row=0, column=0, sticky="NESW")
        #Text for the semicolon section
        self.semiText = tkinter.Label(self.semiFrame, text="Column : ;  Decimal : ,")
        self.semiText.grid(row=1, column=0, sticky="NESW")
        #Button to select semicolon
        self.semiButton = tkinter.Button(self.semiFrame, text="Choose", command=lambda x = False:self.changeSeparators(x))
        self.semiButton.grid(row=2, column=0)
        #Widthdraw separators window
        self.closeSeparators()

        """Add main frames to interface"""
        self.filesFrame.grid(row=0, column=0, sticky="NESW")
        self.configureFrame.grid(row=0, column=0, sticky="NESW")
        self.viewFrame.grid(row=0, column=0, sticky="NESW")
        self.connectFrame.grid(row=0, column=0, sticky="NESW")

        #Perform a first time scan
        self.performScan()
        #If the file display is currently open
        self.filesOpen = False
        #Perfom setup and set down of files to correctly size all elements
        self.setupFiles(self.files, True)
        self.setdownFiles()
        #Create, but do not start, thread to check valve information. If started now it will not be connected and terminate immediately
        self.valveUpdateThread = Thread(target=self.updateValveInfoButton, daemon=True)
        #Which screen is currently being viewed
        self.currentMain = 0
        #Move to the connect screen
        self.changeMainFrame(0)

    def pathTo(self, path : str) -> str:
        '''Convert local path to compiled or directory path'''
        try:
            return os.path.join(sys._MEIPASS, path)
        except:
            return os.path.join(os.path.abspath("."), path)

    def changeMainFrame(self, window : int) -> None:
        """Change the currently displayed screen if a valid index is given"""
        if window == 0:
            self.connectFrame.tkraise()
        if window == 1:
            self.viewFrame.tkraise()
        if window == 2:
            self.configureFrame.tkraise()
        if window == 3:
            self.filesFrame.tkraise()
        #Removes focus from any widget
        self.focus()
        #Store the window index so it can be checked later to identify the current screen
        self.currentMain = window

    def displayMessage(self, title : str, message : str) -> None:
        '''Send user a popup notification with the current title and message, including the icon'''
        notification = notifypy.Notify()
        notification.title = title
        notification.message = message
        notification.icon = self.pathTo("images/icon.png")
        notification.send()

    def moveGasBars(self, channel : int, ch4 : int, co2: int) -> None:
        """Change the position of the bars and gas percentage labels for the given channel"""
        #If it is a valid channel index
        if channel > -1 and channel < len(self.percentageViews):
            #Calculate bar height and position (as percentage of parent) for ch4 and co2
            ch4Height = ch4 / 100.0
            ch4YPos = 1.0 - ch4Height
            co2Height = co2 / 100.0
            co2YPos = 1.0 - co2Height
            #Move the bars and change the percentages
            self.percentageViews[channel]["ch4Bar"].place(rely=ch4YPos, relheight=ch4Height, relwidth=1.0)
            self.percentageViews[channel]["co2Bar"].place(rely=co2YPos, relheight=co2Height, relwidth=1.0)
            self.percentageViews[channel]["ch4Text"].configure(text="{0}%".format(ch4))
            self.percentageViews[channel]["co2Text"].configure(text="{0}%".format(co2))

    def methanePointsPressed(self, channel : int) -> None:
        """Open the graph for methane for the given channel"""
        self.openGraph(channel, True)

    def carbonPointsPressed(self, channel : int) -> None:
        """Open the graph for carbon dioxide for the given channel"""
        self.openGraph(channel, False)

    def checkConnection(self) -> None:
        '''Check if a connection has been made repeatedly until timeout'''
        #If still waiting
        if self.awaitingCommunication:
            #If timeout has been reached or exceeded
            if self.timesTried >= self.timeoutAttempts:
                #Close the connection
                self.serialConnection.close()
                self.serialConnection = None
                self.connected = False
                self.awaiting = False
                self.awaitingCommunication = False
                if self.filesOpen:
                    self.setdownFiles()
                #Display message to user to indicate that connection was lost (Occurs when connecting to a port that is not a chimera)
                self.displayMessage("Connection not established", "Please check this is the correct port and try again.")
                #Return to connect screen
                self.performScan()
                self.changeMainFrame(0)
            else:
                #Increment timeout
                self.timesTried = self.timesTried + 1
                #Test again in .5 seconds
                self.after(500, self.checkConnection)

    def connectPressed(self) -> None:
        '''Attempt to connect to selected port'''
        #If a connection does not already exist
        if not self.connected:
            #If the current port selected exists
            if self.portLabels.index(self.selectedPort.get()) > 0:
                #Set the port of the connection
                self.connectedPort = self.selectedPort.get()
                success = True
                try:
                    #Attempt to connect
                    self.serialConnection = serial.Serial(port=self.connectedPort, baudrate=115200)
                except:
                    #If something went wrong
                    success = False
            
                if success:
                    self.connected = True
                    #Do not allow action if waiting
                    self.awaiting = True
                    self.timesTried = 0
                    self.awaitingCommunication = True
                    self.checkConnection()
                    #Start reading from the port
                    readThread = Thread(target=self.readSerial, daemon=True)
                    readThread.start()
                    #Start handling incoming messages
                    messageThread = Thread(target=self.checkMessages, daemon=True)
                    messageThread.start()
                    #Send connection information request
                    self.sendMessage("info\n")
                else:
                    #Connection failed - reset
                    self.connected = False
                    #Not currently connected to a port
                    self.connectedPort = ""
                    self.displayMessage("Failed to connect", "Check the device is still connected and the port is available.")
                    #Restart scanning for ports
                    self.performScan()
    
    def performScan(self) -> None:
        '''Perform a scan of available ports and update option list accordingly'''
        if not self.connected:
            #List to contain available ports
            found = ["No Port Selected"]
            descs = [""]
            #Scan to find all available ports
            portData = list_ports.comports(include_links=True)
            #Iterate through ports
            for data in portData:
                #Add the device name of the port to the list (can be used to connect to it)
                found.append(data.device)
                descs.append("(" + data.description + ")")
            #If the old and new lists are different
            different = False
            #Test if the lists are different lengths
            if len(found) != len(self.portLabels):
                different = True
            else:
                #Iterate through
                for item in found:
                    #Check if they contain the same things (order unimportant)
                    if item not in self.portLabels:
                        different = True
            #If there was a change
            if different:
                #Update labels
                self.portLabels = found
                #Delete the old menu options
                menu = self.portOption["menu"]
                menu.delete(0, tkinter.END)
                i = 0
                #Iterate through labels
                for name in self.portLabels:
                    #Add the labels to the list
                    menu.add_command(label=name + " " + descs[i], command=lambda v=self.selectedPort, l=name: v.set(l))
                    i = i + 1
                #If the selected item is still available
                if self.selectedPort.get() in self.portLabels:
                    #Set the drop down value to what it was
                    self.selectedPort.set(self.selectedPort.get())
                else:
                    #Set selected option to none
                    self.selectedPort.set(self.portLabels[0])
            
            #Scan again shortly
            self.after(150, self.performScan)

    def trySelectPort(self, portName) -> None:
        '''Attempt to select a given port name - if it still exists'''
        #If not already connected to a device
        if not self.connected:
            #If the port name exists
            if portName in self.portLabels:
                #Switch to that port as selected
                self.selectedPort.set(portName)

    def configurePressed(self) -> None:
        '''Enter configure mode and send messages to gas sensor accordingly'''
        if self.connected and not self.awaiting:
            if not self.calibrating:
                #Requests for information so it is as up to date as possible
                self.sendMessage("timeget\n")
                self.sendMessage("timingget\n")
                self.sendMessage("startcal\n")
                self.awaiting = True
                self.calibrationUpdated = False
    
    def endConfigurePressed(self) -> None:
        if self.connected and not self.awaiting:
            self.sendMessage("endcal\n")
            self.awaiting = True
    
    def viewFilesPressed(self) -> None:
        if self.connected and not self.awaiting:
            self.sendMessage("timeget\n")
            self.askForFiles()
            self.awaitingFiles = True
            self.awaiting = True
    
    def setTimePressed(self) -> None:
        '''If in calibration mode - send the time from the computer to the gas sensor to set the real time clock'''
        if self.connected and not self.awaiting:
            if self.calibrating:
                time = datetime.datetime.now()
                self.sendMessage("timeset {0},{1},{2},{3},{4},{5}\n".format(time.year, time.month, time.day, time.hour, time.minute, time.second))
                self.awaiting = True


    def askForFiles(self) -> None:
        '''Ask the esp32 for the list of held files'''
        #If there is a connection
        if self.connected and self.serialConnection != None:
            #If not waiting for a response
            if not self.awaiting:
                self.files = []
                self.fileSizes = []
                #Ask for the list of files
                self.sendMessage("files\n")
                self.awaiting = True

    def deletePressed(self) -> None:
        '''Delete the currently selected file from the memory'''
        #If the connection is running
        if self.connected and self.serialConnection != None:
            #If not waiting for a response
            if not self.awaiting:
                #If there is a file selected (and a valid one)
                if self.selectedFile != -1 and len(self.files) > self.selectedFile:
                    #Ask for confirmation
                    confirm = messagebox.askyesno(title="Confirm Delete", message="Are you sure you want to delete " + self.files[self.selectedFile] + "?\nThis action cannot be undone.")
                    if confirm:
                        #Send signal to delete file
                        message = "delete " + "/files/" + self.files[self.selectedFile] + "\n"
                        self.sendMessage(message)
                        #Wait for confirmation of deletion
                        self.awaiting = True
                else:
                    self.displayMessage("No File Selected", "Please select a file to delete.")
        else:
            self.displayMessage("Not Connected", "You must be connected to a port to delete files.")

    def downloadPressed(self) -> None:
        '''Send request to download the selected file to the computer'''
        #If there is a connection
        if self.connected and self.serialConnection != None:
            #If not waiting for a response
            if not self.awaiting:
                #If a file has been selected (and a valid one)
                if self.selectedFile != -1 and len(self.files) > self.selectedFile:
                    #Default name to save file as - same as the file name on the esp32
                    defaultName = self.files[self.selectedFile]
                    defaultName = defaultName.replace(".csv", "")
                    defaultName = defaultName.replace(".txt", "")
                    #Ask where to save the file
                    path = filedialog.asksaveasfilename(title="Save file location", filetypes=self.fileTypes, defaultextension=self.fileTypes, initialfile=defaultName)
                    #Remove whitespace
                    path = path.strip()
                    #If there is a file name
                    if path != None and path != "":
                        #If it doesn't have a .csv extension for some reason - then add one
                        if not path.endswith(".csv"):
                            path = path + ".csv"
                        #Store the save path
                        self.fileNameToSave = path
                        #Send message to download
                        message = "download " + "/files/" + self.files[self.selectedFile] + "\n"
                        self.sendMessage(message)
                        self.awaiting = True
                        self.downloadFileButton.configure(state="disabled")
                else:
                    self.displayMessage("No File Selected", "Please select a file to download.")
        else:
            self.displayMessage("Not Connected", "You must be connected to a port to download files.")
    
    def updateTimingsDisplay(self) -> None:
        self.openTimeLabel.configure(text="Open Time: {0}s".format(self.currentOpen))
        self.flushTimeLabel.configure(text="Open Time: {0}s".format(self.currentFlush))
        self.openTimeEntry.delete(0, "end")
        self.flushTimeEntry.delete(0, "end")
        self.openTimeEntry.insert(0, str(self.currentOpen))
        self.flushTimeEntry.insert(0, str(self.currentFlush))
    
    def sendMessage(self, message : str) -> None:
        if self.connected and self.serialConnection != None:
            self.serialConnection.write(message.encode("utf-8"))

    def readSerial(self) -> None:
        '''While connected repeatedly read information from serial connection'''
        #If there is a connection
        if self.connected and self.serialConnection != None:
            #Attempt
            try:
                done = False
                #Until out of data
                while not done:
                    #Read the next character
                    char = self.serialConnection.read()
                    #If there is a character
                    if len(char) > 0:
                        try:
                            #Attempt from byte to string and print
                            ch = char.decode("utf-8")
                            if ch == "\n":
                                #Add to list of messages
                                self.receivedMessages.append(self.currentMessage)
                                self.currentMessage = ""
                            else:
                                self.currentMessage = self.currentMessage + ch
                        except:
                            #If it failed an unusual escape character has been read and it is simply ignored
                            pass
                    else:
                        #Finished reading - end of stream reached
                        done = True
                
                #Repeat this read function after 10ms
                self.after(10, self.readSerial)
            except:
                #Close the connection and reset the buttons
                self.serialConnection.close()
                self.serialConnection = None
                self.connected = False
                if self.filesOpen:
                    self.setdownFiles()
                #Display message to user to indicate that connection was lost (Occurs when device unplugged)
                self.displayMessage("Connection Lost", "Please check connection and try again.")
                self.closeWindow()

    def checkMessages(self) -> None:
        '''Repeatedly check for a new message and handle it'''
        #If there is a message
        if len(self.receivedMessages) > 0:
            #Get the message
            nextMessage = self.receivedMessages[0]
            #Handle based on what the message is
            self.messageReceived(nextMessage)
            #Remove message from the list
            del self.receivedMessages[0]
        #If there is still a connection
        if self.serialConnection != None:
            #Repeat after a short delay
            self.after(1, self.checkMessages)

    def messageReceived(self, message) -> None:
        #DEBUG display the message
        print(message)
        #Split up the message into parts on spaces
        messageParts = message.split(" ")
        #If this is the information about the state of the esp32
        if len(messageParts) > 1 and messageParts[0] == "info":

            #If waiting for the response from the device
            if self.awaitingCommunication:
                #No longer waiting
                self.awaitingCommunication = False
                #Send request for past data
                self.sendMessage("getpast\n")
                self.sendMessage("timingget\n")
                self.sendMessage("serviceget\n")
                self.sendMessage("getcal\n")
                self.parent.title("Chimera Client - {0}".format(self.connectedPort))
                #Display connected message
                self.displayMessage("Connected successfully", "Now viewing device information")
                self.valveUpdateThread.start()

                #For each of the channels
                for i in range(0, 15):
                    #Set colour to default colour
                    col = self.defaultButtonColour
                    if not self.currentService[i]:
                        col = self.darkenedColour
                    #Update the background of each part
                    self.percentageViews[i]["frame"].configure(bg=col)
                    self.percentageViews[i]["label"].configure(bg=col)
                    self.percentageViews[i]["ch4"].configure(bg=col)
                    self.percentageViews[i]["co2"].configure(bg=col)
                    self.percentageViews[i]["ch4Out"].configure(bg=col)
                    self.percentageViews[i]["co2Out"].configure(bg=col)
                    self.percentageViews[i]["ch4Text"].configure(bg=col)
                    self.percentageViews[i]["co2Text"].configure(bg=col)

            if messageParts[1] == "true":
                #Calibrating state
                self.calibrating = True
                self.switchToConfiguring()
            else:
                self.changeMainFrame(1)

            try:
                #Attempt to get the number of the valve currently open
                valveCurrentlyOpen = int(messageParts[2])
                #Iterate through and set valve open state
                for i in range(0, len(self.valveStates)):
                    self.valveStates[i] = i == valveCurrentlyOpen
                #Change the label to reflect current valve
                self.updateValveLabel()
            except:
                pass
                
            if len(messageParts) > 2:
                lastEventDifference = 0.0
                try:
                    lastEventDifference = int(messageParts[3]) / 1000.0
                except:
                    pass
                print("Difference:", lastEventDifference)
                self.lastEvent = time.time() - lastEventDifference
                print(self.lastEvent)
            
            #No longer waiting for a response
            self.awaiting = False
            #Cycle the files so they are up to date
            self.setdownFiles()
            #self.askForFiles()
        
        #If an action has been successfully performed
        if len(messageParts) > 1 and messageParts[0] == "done":
            #No longer waiting for a response
            self.awaiting = False
            #Finished sending files
            if messageParts[1] == "files":
                #Display the files that were received
                self.setupFiles(self.files)
                if self.awaitingFiles and self.currentMain == 1:
                    self.changeMainFrame(3)
                self.awaitingFiles = False

            #Finished deleting file
            if messageParts[1] == "delete":
                #Show message that files were deleted
                self.displayMessage("File Deleted", "File was deleted sucessfully.")
                self.setdownFiles()
                self.askForFiles()
            
            #Finished entering calibration mode
            if messageParts[1] == "startcal":
                self.calibrating = True
                #Open calibration interface
                self.switchToConfiguring()
            
            #Finished exiting calibration mode
            if messageParts[1] == "endcal":
                self.calibrating = False
                #Return to main view
                self.switchToView()
                #self.askForFiles()
            
            #Time was set successfully
            if messageParts[1] == "timeset":
                self.displayMessage("Time Set", "Clock time was updated successfully.")
                self.sendMessage("timeget\n")
                self.awaiting = False
            
            #Valve timing was successfully changed
            if messageParts[1] == "timingset":
                self.displayMessage("Timing Set", "Valve opening times updated successfully.")
                self.awaiting = False
            
            #Calibration was set successfully
            if messageParts[1] == "calset":
                self.displayMessage("Calibration Set", "Successfully updated calibration.")
                self.closeCalculations()
                self.awaiting = False
            
            #In service was set successfully
            if messageParts[1] == "serviceset":
                #self.displayMessage("Channel Service Set", "Successfully updated which channels are in service.")
                #self.closeService()
                self.sendMessage("serviceget\n")
        
        #If an action failed with an error message
        if len(messageParts) > 2 and messageParts[0] == "failed":
            if messageParts[1] == "download":
                if messageParts[2] == "nofile":
                    self.displayMessage("File Not Found", "Download stopped.")
                    self.downloadFileButton.configure(state="normal")
                self.downloading = False
            if messageParts[1] == "delete":
                if messageParts[2] == "nofile":
                    self.displayMessage("File Not Found", "Delete action could not be completed.")
            
            if messageParts[1] == "calset":
                if messageParts[2] == "invalidtype":
                    self.displayMessage("Error Occurred", "There was an error while attempting to set the calibration, please try again.")
                if messageParts[2] == "notcalibrating":
                    self.displayMessage("Error Occurred", "Something went wrong while trying to calibrate, please try again.")
                    self.calibrating = False
                    self.switchToView()
            
            if messageParts[1] == "timeset":
                if messageParts[2] == "notcalibrating":
                    self.calibrating = True
                    self.switchToView()
            
            if messageParts[1] == "startcal":
                if messageParts[2] == "calibrating":
                    self.calibrating = True
                    self.switchToConfiguring()
            
            if messageParts[1] == "endcal":
                if messageParts[2] == "notcalibrating":
                    self.calibrating = False
                    self.switchToView()
            
            if messageParts[1] == "point":
                if messageParts[2] == "invalidtype":
                    self.displayMessage("Unable To Get Data.", "Something went wrong while trying to start reading, please try again.")
                if messageParts[2] == "alreadychecking":
                    self.displayMessage("Already Reading.", "Cannot attempt to calibrate for two points at once, please wait and try again.")
                if messageParts[2] == "notcalibrating":
                    self.calibrating = False
                    self.switchToView()
                    #self.askForFiles()
            
            if messageParts[1] == "timingset":
                if messageParts[2] == "noopen":
                    self.displayMessage("Could Not Set Timing", "No open time value was found, please try again.")
                if messageParts[2] == "noflush":
                    self.displayMessage("Could Not Set Timing", "No flush time value was found, please try again.")
                if messageParts[2] == "notcalibrationg":
                    self.calibrating = False
                    self.switchToView()
            
            if messageParts[1] == "timingget":
                if messageParts[2] == "notcalibrating":
                    self.calibrating = False
                    self.switchToView()    
            
            if messageParts[1] == "serviceset":
                if messageParts[2] == "notcalibrating":
                    self.calibrating = False
                    self.switchToView()
            
            #No longer waiting for a response
            self.awaiting = False

        #If it is a file name being given
        if len(messageParts) > 1 and messageParts[0] == "file":
            #If this is not the start of the files
            if messageParts[1] != "start":
                #Add to the list
                self.files.append(messageParts[1])
                size = -1
                if len(messageParts) > 2:
                    try:
                        size = int(messageParts[2])
                    except:
                        pass
                self.fileSizes.append(size)
            else:
                #Reset the files and await file data
                self.setdownFiles()
                self.files = []
                self.fileSizes = []
                self.awaiting = True

        
        #If it is part of the file download sequence
        if len(messageParts) > 1 and messageParts[0] == "download":
            #If it is a new file
            if len(messageParts) > 3 and messageParts[1] == "start":
                #Reset the file data
                self.fileDataToSave = ""
                #Currently downloading a file
                self.downloading = True
                #Get the total number of characters to be received
                totalCharacters = int(messageParts[3])
                #Configure the progress bar correctly
                self.setupProgressBar(totalCharacters)
                #No characters have been downloaded yet
                self.downloadedCharacters = 0
                self.currentLine = 0
            #If it is the end of a file
            elif messageParts[1] == "stop":
                #Attempt to save the file
                try:
                    #Open the file to write
                    saveFile = open(self.fileNameToSave, "w")
                    data = self.fileDataToSave
                    if not self.comma:
                        lines = data.split("\n")
                        for ln in range(0, len(lines)):
                            parts = lines[ln].split(",")
                            for i in range(0, len(parts)):
                                parts[i] = parts[i].replace(".", ",")
                            lines[ln] = ";".join(parts)
                        data = "\n".join(lines)
                    #Write the data
                    saveFile.write(data)
                    #Close the file
                    saveFile.close()
                    #Success message
                    self.displayMessage("Download Successful", "File successfully downloaded.")
                except:
                    #Something went wrong - failed message
                    self.displayMessage("Download Failed", "File was not downloaded correctly, please try again.")
                
                #No longer downloading or waiting for a response
                self.downloading = False
                self.awaiting = False
                #Remove the progress bar
                self.setdownProgressBar()
                #Reset the download button
                self.downloadFileButton.configure(state="normal")
            elif messageParts[1] == "failed":
                #Something went wrong - failed message
                self.displayMessage("Download Failed", "File was not downloaded correctly, timeout occurred.")
                self.downloading = False
                self.awaiting = False
                self.setdownProgressBar()
                self.downloadFileButton.configure(state="normal")
            #Otherwise it is a line in the file (if currently expecting data)
            elif self.downloading:
                #Iterate through parts (except for first)
                for i in range(1, len(messageParts)):
                    self.downloadedCharacters = self.downloadedCharacters + len(messageParts[i]) + 1
                    #messageParts[i] = messageParts[i].replace(".", self.decimal).replace(":", self.decimal)
                    #Remove any carriage returns
                    self.fileDataToSave = self.fileDataToSave + messageParts[i].replace("\r", "")
                    #If this is not the last in the message
                    if i != len(messageParts) - 1:
                        #Add a comma
                        self.fileDataToSave = self.fileDataToSave + ","
                        #self.fileDataToSave = self.fileDataToSave + self.column
                    else:
                        #Add a new line
                        self.fileDataToSave = self.fileDataToSave + "\n"
                
                self.currentLine = self.currentLine + 1
                self.sendMessage("next\n")
                self.after(3000, self.reattemptNextLine, self.currentLine, 0)

        #If this is information regarding the memory
        if len(messageParts) > 2 and messageParts[0] == "memory":
            try:
                #Attempt to convert values to integers
                total = int(messageParts[1])
                used = int(messageParts[2])
                #Calculate percentage used
                percentage = int((used / total) * 100)
                #Calculate the total memory in MegaBytes
                total = int(total / 100000) / 10
                #Calculate the used memory in MegaBytes
                used = int(used / 100000) / 10
                self.sdCardInfoLabel.configure(text=self.sdCardString.format(used, total, percentage))
            except:
                #If something went wrong (not an integer) do not update the memory
                pass
        
        #If a calibration point was received
        if len(messageParts) > 2 and messageParts[0] == "calpoint":
            try:
                #Convert the value given to an integer
                value = int(messageParts[2])
                #Methane point
                if messageParts[1] == "ch4":
                    #Store the value and percentage
                    self.ch4Values.append(value)
                    self.ch4Percentages.append(self.percentageValue)
                    #Update the regression calculation
                    self.calculatePolynomials(True)
                    self.displayMessage("Point Received Sucessfully.", "A value of {0} was received for a concentration of {1}% methane.".format(value, self.percentageValue))
                    self.awaiting = False
                    #Clear and redraw methane calibration graph
                    self.ch4CalPlot.clear()
                    for i in range(0, len(self.ch4Values)):
                        if i < len(self.ch4Percentages):
                            self.ch4CalPlot.scatter(self.ch4Values[i], self.ch4Percentages[i], c="blue")
                    self.ch4CalPlot.set_title("Methane Calibration")
                    #If there is a suitable regression, draw its curve
                    if len(self.ch4Percentages) > 1:
                        self.ch4CalPlot.plot(self.ch4PlotPoints[0], self.ch4PlotPoints[1], c="red")
                    self.ch4CalCanvas.draw()
                #Carbon dioxide point
                elif messageParts[1] == "co2":
                    #Store the value and percentage
                    self.co2Values.append(value)
                    self.co2Percentages.append(self.percentageValue)
                    #Update the regression calculation
                    self.calculatePolynomials(False)
                    self.displayMessage("Point Received Sucessfully.", "A value of {0} was received for a concentration of {1}% carbon dioxide.".format(value, self.percentageValue))
                    self.awaiting = False
                    #Clear and redraw carbon dioxide calibration graph
                    self.co2CalPlot.clear()
                    for i in range(0, len(self.co2Values)):
                        if i < len(self.co2Percentages):
                            self.co2CalPlot.scatter(self.co2Values[i], self.co2Percentages[i], c="blue")
                    self.co2CalPlot.set_title("Carbon Dioxide Calibration")
                    #If there is a suitable regression, draw its curve
                    if len(self.co2Percentages) > 1:
                        self.co2CalPlot.plot(self.co2PlotPoints[0], self.co2PlotPoints[1], c="red")
                    self.co2CalCanvas.draw()
            except:
                pass
        
        #If there is a datapoint to be stored for debugging peaks
        if len(messageParts) > 5 and messageParts[0] == "dataPoint":
            '''datapoint valveNumber CH4Maximum CO2Maximum CH4Percent CO2Percent CH4Peak1 CH4Peak2 CH4Peak3 CH4Peak4 CH4Peak5 CO2Peak1 CO2Peak2 CO2Peak3 CO2Peak4 CO2Peak5'''
            try:
                #Convert each value into an integer
                ch4 = int(float(messageParts[4]))
                co2 = int(float(messageParts[5]))
                channel = int(messageParts[1])
                #Add to view percentages
                self.moveGasBars(channel, ch4, co2)
                #Iterate through channels
                for i in range(0, 16):
                    #Set colour to selected only if this is the current channel
                    col = self.defaultButtonColour
                    if i == channel:
                        col = self.selectedButtonColour
                    else:
                        if i != 15:
                            if not self.currentService[i]:
                                col = self.darkenedColour
                    #Update the background of each part
                    self.percentageViews[i]["frame"].configure(bg=col)
                    self.percentageViews[i]["label"].configure(bg=col)
                    self.percentageViews[i]["ch4"].configure(bg=col)
                    self.percentageViews[i]["co2"].configure(bg=col)
                    self.percentageViews[i]["ch4Out"].configure(bg=col)
                    self.percentageViews[i]["co2Out"].configure(bg=col)
                    self.percentageViews[i]["ch4Text"].configure(bg=col)
                    self.percentageViews[i]["co2Text"].configure(bg=col)
                
                #If there are enough values for each of the 5 extra points per gas type
                if len(messageParts) > 15:
                    numberItems = 5
                    self.ch4DebugData[channel] = []
                    self.co2DebugData[channel] = []
                    ch4Start = 6
                    co2Start = ch4Start + numberItems
                    #Collect each of the values for the peak data around the values
                    for i in range(ch4Start, ch4Start + numberItems):
                        if len(messageParts) > i:
                            self.ch4DebugData[channel].append(int(float(messageParts[i])))
                    for i in range(co2Start, co2Start + numberItems):
                        if len(messageParts) > i:
                            self.co2DebugData[channel].append(int(float(messageParts[i])))
            except Exception as e:
                print(e)
        
        #If this is a message about the current timing of the valves
        if len(messageParts) > 2 and messageParts[0] == "timing":
            try:
                #Convert from ms to s
                openValue = int(int(messageParts[1]) / 1000)
                flushValue = int(int(messageParts[2]) / 1000)
                #Store open and flush times
                self.currentOpen = openValue
                self.currentFlush = flushValue
                self.awaiting = False
                self.updateTimingsDisplay()
            except:
                self.displayMessage("Could Not Retrieve Timings", "Could not get timings from device, please try again.")

            self.awaiting = False

        #If this is the channels in service being updated
        if len(messageParts) > 15 and messageParts[0] == "service":
            #Iterate through characters
            for i in range(0, 15):
                #If the character is not a 0 then the channel is in service
                self.currentService[i] = messageParts[i + 1] != "0"
            #Open the window to display this information
            #self.openServiceWindow()
            self.updateServiceDisplays()
            self.awaiting = False
        
        #If this is a message conveying the current calibration data
        if len(messageParts) > 8 and messageParts[0] == "currentcal":
            try:
                #Iterate for each type of gas and store values
                for i in range(1, 5):
                    self.storedCalibration[0][i - 5] = float(messageParts[i])
                for i in range(5, 9):
                    self.storedCalibration[1][i - 5] = float(messageParts[i])
                #Calibration has been updated recently
                self.calibrationUpdated = True
            except:
                print("Invalid calibration data passed, ignored safely")
        
        #If this is a message conveying the past data for each channel
        if len(messageParts) > 30 and messageParts[0] == "pastdata":
            try:
                #Iterate through channels
                for channel in range(0, 16):
                    #Get values from device
                    ch4 = int(messageParts[(channel * 2) + 1])
                    co2 = int(messageParts[(channel * 2) + 2])
                    #Add to view percentages
                    self.moveGasBars(channel, ch4, co2)

            except:
                print("Invalid past data, ignored safely")
        
        #If this is a message about valves opening or closing
        if len(messageParts) > 2 and messageParts[0] == "valve":
            #Attempt to get valve data
            try:
                #Get the valve index as a number
                changedValve = int(messageParts[1])
                #If it was changed correctly
                if messageParts[2] in ["opened", "closed"]:
                    #Iterate all valves
                    for i in range(0, len(self.valveStates)):
                        #Set the valve states (true if it was this valve and opened, otherwise false)
                        self.valveStates[i] = i == changedValve and messageParts[2] == "opened"
                    #Update the label to display correctly
                    self.updateValveLabel()
                    self.lastEvent = time.time()
                    if self.calibratingPoint:
                        if changedValve == 0 and messageParts[2] == "opened":
                            self.calibrationActionTime = time.time()
                            self.calibrationReading = True
                            self.calibrationFlushing = False
                        elif self.calibrationReading and changedValve == 0 and messageParts[2] == "closed":
                            self.calibrationReading = False
                        elif changedValve == 15 and messageParts[2] == "opened":
                            self.calibrationActionTime = time.time()
                            self.calibrationFlushing = True
                            self.calibrationReading = False
                        elif self.calibrationFlushing and changedValve == 15 and messageParts[2] == "closed":
                            self.calibrationFlushing = False
                            self.calibrationReading = False
                            self.calibratingPoint = False
                            
            except:
                #Ignore invalid valve data with no error
                pass
        
        if len(messageParts) > 1 and messageParts[0] == "time":
            try:
                timeParts = messageParts[1].split(",")
                year = int(timeParts[0])
                month = int(timeParts[1])
                day = int(timeParts[2])
                hour = int(timeParts[3])
                minute = int(timeParts[4])
                second = int(timeParts[5])
                self.currentClockTimeLabel.configure(text="Current: {0}:{1}:{2} {3}/{4}/{5}".format(hour, minute, second, day, month, year))
                if month < 9:
                    month = "0" + str(month)
                self.currentTimeFileName = "eventLog_{0}{1}.csv".format(year, month)
            except:
                if self.connected and self.serialConnection != None:
                    self.sendMessage("timeget\n")

        
    def reattemptNextLine(self, lineNumber, count) -> None:
        '''Attempt to download a line again until timeout reached or line was received'''
        #If they line has not been received and a connection is still present
        if lineNumber == self.currentLine and self.downloading and self.serialConnection != None:
            #Ask for the next line again
            self.sendMessage("next\n")
            #If it has not been retried more than 3 times try again
            if count < 2:
                self.after(3000, self.reattemptNextLine, self.currentLine, count + 1)
                    
    def filePressed(self, index : int) -> None:
        '''When a file is clicked on'''
        #If not currently waiting
        if not self.awaiting:
            #If this is the currently selected file
            if index == self.selectedFile:
                #If it is a valid index
                if index > -1 and index < len(self.fileButtons):
                    #Reset button colour to default (if it exists)
                    if self.fileButtons[index].winfo_exists() == 1:
                        self.fileButtons[index].configure(bg=self.defaultButtonColour)
                #Reset selected file index and label
                self.selectedFile = -1
                self.fileLabel.configure(text="No file selected")
                self.downloadFileButton.configure(state="disabled")
                self.deleteFileButton.configure(state="disabled")
            else:
                #If the index is valid
                if index < len(self.files):
                    #If there is currently a selected file
                    if self.selectedFile != -1:
                        #Deselect current file
                        self.fileButtons[self.selectedFile].configure(bg=self.defaultButtonColour)
                    #Select new file
                    self.selectedFile = index
                    self.fileLabel.configure(text=self.files[index])
                    #Enable button actions
                    self.downloadFileButton.configure(state="normal")
                    self.deleteFileButton.configure(state="normal")
                    self.fileButtons[index].configure(bg=self.selectedButtonColour)

    def disconnect(self) -> None:
        '''Close connection to port'''
        #If there is a connection and there is not data to be recieved
        if self.connected and not self.awaiting:
            #If there is a serial connection object
            if self.serialConnection != None:
                #Close the connection
                self.serialConnection.close()
                self.serialConnection = None
            #Switch buttons so disconnect is disabled and connect is enabled
            self.connected = False
            if self.filesOpen:
                self.setdownFiles()
            #Display message to indicate that the connection has been closed
            self.displayMessage("Connection Closed", "The connection has been terminated successfully.")
            self.parent.destroy()

    def switchToConfiguring(self) -> None:
        '''Change to display the calibration window and alter the button text'''
        if self.connected and self.serialConnection != None:
            self.sendMessage("timeget\n")
        self.changeMainFrame(2)

    def switchToView(self) -> None:
        '''Change to display the view window and alter the button text'''
        self.changeMainFrame(1)
    
    def addPointPressed(self, methane : bool) -> None:
        if not self.awaiting:
            if methane:
                self.setupCh4PointFrame.tkraise()
            else:
                self.setupCo2PointFrame.tkraise()
    
    def cancelPointPressed(self, methane : bool) -> None:
        if not self.awaiting:
            if methane:
                self.addCh4PointButtonFrame.tkraise()
            else:
                self.addCo2PointButtonFrame.tkraise()
    
    def openAddPercentage(self, methane : bool) -> None:
        if not self.awaiting:
            if methane:
                self.ch4AddPercent = -1
                self.ch4AddValue = -1
                self.setupValueEntryCh4PointLabel.configure(text="Percentage:")
                self.setupValueEntryCh4PointEntry.delete(0, tkinter.END)
                self.setupValueEntryCh4PointEntry.insert("0", 0)
                self.setupValueEntryCh4PointFrame.tkraise()
            else:
                self.co2AddPercent = -1
                self.co2AddValue = -1
                self.setupValueEntryCo2PointLabel.configure(text="Percentage:")
                self.setupValueEntryCo2PointEntry.delete(0, tkinter.END)
                self.setupValueEntryCo2PointEntry.insert("0", 0)
                self.setupValueEntryCo2PointFrame.tkraise()
    
    def openAddValue(self, methane : bool) -> None:
        if not self.awaiting:
            if methane:
                self.setupValueEntryCh4PointLabel.configure(text="Millivolts:")
                self.setupValueEntryCh4PointEntry.delete(0, tkinter.END)
                self.setupValueEntryCh4PointEntry.insert("0", 0)
                self.setupValueEntryCh4PointFrame.tkraise()
            else:
                self.setupValueEntryCo2PointLabel.configure(text="Millivolts:")
                self.setupValueEntryCo2PointEntry.delete(0, tkinter.END)
                self.setupValueEntryCo2PointEntry.insert("0", 0)
                self.setupValueEntryCo2PointFrame.tkraise()
    
    def manualPressed(self, methane : bool) -> None:
        if not self.awaiting:
            if methane:
                self.ch4AddType = "man"
            else:
                self.co2AddType = "man"

        self.openAddPercentage(methane)

    def automaticPressed(self, methane : bool) -> None:
        if not self.awaiting:
            if methane:
                self.ch4AddType = "auto"
            else:
                self.co2AddType = "auto"
        
        self.openAddPercentage(methane)
    
    def valueAddConfirmPressed(self, methane : bool) -> None:
        if not self.awaiting:
            if (methane and self.ch4AddPercent == -1) or ((not methane) and self.co2AddPercent == -1):
                maximum = 100
            else:
                maximum = 8191
            enteredValue = -1
            failed = False
            try:
                if methane:
                    valueFromEntry = self.setupValueEntryCh4PointEntry.get()
                else:
                    valueFromEntry = self.setupValueEntryCo2PointEntry.get()
                if len(valueFromEntry) > 0:
                    enteredValue = int(valueFromEntry)
                else:
                    self.displayMessage("Invalid Value", "Must enter a number")
            except:
                self.displayMessage("Invalid Value", "Must enter a number")
                failed = True
            if not failed:
                if enteredValue > -1 and enteredValue <= maximum:
                    if (methane and self.ch4AddPercent == -1) or ((not methane) and self.co2AddPercent == -1):
                        if methane:
                            print("Setting percentage")
                            self.ch4AddPercent = enteredValue
                        else:
                            self.co2AddPercent = enteredValue
                        if (methane and self.ch4AddType == "auto") or (not methane and self.co2AddType == "auto"):
                            if methane:
                                self.sendMessage("point ch4 {0}\n".format(self.calibrationReadTime * 1000))
                            else:
                                self.sendMessage("point co2 {0}\n".format(self.calibrationReadTime * 1000))
                            self.awaiting = True
                            self.percentageValue = enteredValue
                            self.calibratingMethane = methane
                            self.setupCalibrationTiming()
                        else:
                            self.openAddValue(methane)
                    else:
                        if methane:
                            self.ch4AddValue = enteredValue
                        else:
                            self.co2AddValue = enteredValue
                        self.addPointValues(methane)
                else:
                    self.displayMessage("Invalid Value", "Must be between 0 and {0}".format(maximum))
    
    def addPointValues(self, methane : bool) -> None:
        if methane:
            self.ch4Percentages.append(self.ch4AddPercent)
            self.ch4Values.append(self.ch4AddValue)
            self.ch4AddPercent = -1
            self.ch4AddValue = -1
        else:
            self.co2Percentages.append(self.co2AddPercent)
            self.co2Values.append(self.co2AddValue)
            self.ch4AddPercent = -1
            self.ch4AddValue = -1

        self.cancelPointPressed(methane)
        
        self.calculatePolynomials(methane)
        self.updateGraph(methane)

    def updateGraph(self, methane : bool) -> None:
        if methane:
            self.ch4CalPlot.clear()
            for i in range(0, len(self.ch4Values)):
                if i < len(self.ch4Percentages):
                    self.ch4CalPlot.scatter(self.ch4Values[i], self.ch4Percentages[i], c="blue")
            self.ch4CalPlot.set_title("Methane Calibration")
            #If there is a suitable regression - display it too
            if len(self.ch4Percentages) > 1:
                self.ch4CalPlot.plot(self.ch4PlotPoints[0], self.ch4PlotPoints[1], c="red")
            self.ch4CalCanvas.draw()
        else:
            self.co2CalPlot.clear()
            for i in range(0, len(self.co2Values)):
                if i < len(self.co2Percentages):
                    self.co2CalPlot.scatter(self.co2Values[i], self.co2Percentages[i], c="blue")
            self.co2CalPlot.set_title("Carbon Dioxide Calibration")
            if len(self.co2Percentages) > 1:
                self.co2CalPlot.plot(self.co2PlotPoints[0], self.co2PlotPoints[1], c="red")
            self.co2CalCanvas.draw()

    def setupCalibrationTiming(self) -> None:
        self.calibrationActionTime = time.time()
        if self.calibratingMethane:
            self.setupValueCh4TimingLabel.configure(text="Valve 1 open, reading. {0}s remaining.".format(self.calibrationReadTime))
            self.setupValueCh4TimingFrame.tkraise()
        else:
            self.setupValueCo2TimingLabel.configure(text="Valve 1 open, reading. {0}s remaining.".format(self.calibrationReadTime))
            self.setupValueCo2TimingFrame.tkraise()
        
        self.calibrationReading = True
        self.calibrationFlushing = False
        self.calibratingPoint = True

        self.updateCalibrationTiming()
    
    def updateCalibrationTiming(self) -> None:
        if self.calibrationReading:
            remaining = max(int(self.calibrationReadTime - (time.time() - self.calibrationActionTime)), 0)
            if self.calibratingMethane:
                self.setupValueCh4TimingLabel.configure(text="Valve 1 open, reading. {0}s remaining.".format(remaining))
            else:
                self.setupValueCo2TimingLabel.configure(text="Valve 1 open, reading. {0}s remaining.".format(remaining))
        elif self.calibrationFlushing:
            remaining = max(int(self.calibrationFlushTime - (time.time() - self.calibrationActionTime)), 0)
            if self.calibratingMethane:
                self.setupValueCh4TimingLabel.configure(text="Valve 16 Open, flushing. {0}s remaining.".format(remaining))
            else:
                self.setupValueCo2TimingLabel.configure(text="Valve 16 Open, flushing. {0}s remaining.".format(remaining))
        else:
            if self.calibratingMethane:
                self.setupValueCh4TimingLabel.configure(text="Waiting.")
            else:
                self.setupValueCo2TimingLabel.configure(text="Waiting.")

        if self.calibratingPoint:
            self.after(10, self.updateCalibrationTiming)
        else:
            if self.calibratingMethane:
                self.addCh4PointButtonFrame.tkraise()
            else:
                self.addCo2PointButtonFrame.tkraise()

    def addPointCh4Pressed(self) -> None:
        '''When add button is pressed on methane'''
        #Ask for manual or sensor entry
        response = messagebox.askquestion(title="Manual or Using Sensor", message="Do you want to read the value from the sensor? Sensor is connected to channel 1, otherwise enter the values manually.")
        if response == "yes":
            #Attempt sensor reading for point
            if self.connected and not self.awaiting:
                #Ask the user for a percentage of methane in the gas
                percent = simpledialog.askinteger(title="What Percentage?", prompt="Enter the percentage concentration of methane.", initialvalue=0)
                #Check that the value is a valid integer
                if type(percent) == int:
                    if percent < 0 or percent > 100:
                        self.displayMessage("Invalid Value", "Must be a percentage between 0 and 100.")
                    else:
                        #Ask the user how long to take the reading for
                        time = simpledialog.askinteger(title="How long to read?", prompt="Enter how many seconds to read the sensor value for.", initialvalue=5)
                        #Check it is a valid integer
                        if type(time) == int:
                            if time < 1 or time > 60 * 60:
                                self.displayMessage("Invalid Value", "Must be at least 1 second and no longer than an hour.")
                            else:
                                #Ask the device for a calibration point for methane
                                self.sendMessage("point ch4 {0}\n".format(time * 1000))
                                self.awaiting = True
                                self.percentageValue = percent
        elif response == "no":
            #Add point data manually
            self.addCustomMethane()
    
    def addPointCo2Pressed(self) -> None:
        '''When add button is pressed on carbon dioxide'''
        #Ask for manual or sensor entry
        response = messagebox.askquestion(title="Manual or Using Sensor", message="Do you want to read the value from the sensor? Sensor is connected to channel 1, otherwise enter the values manually.")
        if response == "yes":
            #Attempt sensor reading for point
            if self.connected and not self.awaiting and self.calibrating:
                #Ask the user for a percentage of carbon dioxide in the gas
                percent = simpledialog.askinteger(title="What Percentage?", prompt="Enter the percentage concentration of carbon dioxide.", initialvalue=0)
                #Check that the value is a valid integer
                if type(percent) == int:
                    if percent < 0 or percent > 100:
                        self.displayMessage("Invalid Value", "Must be a percentage between 0 and 100.")
                    else:
                        #Ask the user how long to take the reading for
                        time = simpledialog.askinteger(title="How long to read?", prompt="Enter how many seconds to read the sensor value for.", initialvalue=5)
                        #Check it is a valid integer
                        if type(time) == int:
                            if time < 1 or time > 60 * 60:
                                self.displayMessage("Invalid Value", "Must be at least 1 second and no longer than an hour.")
                            else:
                                #Ask the device for a calibration point for carbon dioxide
                                self.sendMessage("point co2 {0}\n".format(time * 1000))
                                self.awaiting = True
                                self.percentageValue = percent
        elif response == "no":
            #Add the point data manually
            self.addCustomCarbonDioxide()

    def calculatePolynomials(self, methane : bool) -> None:
        '''Perform linear regression on the calibration points if possible'''
        if methane:
            #If there is more than one methane point
            if len(self.ch4Percentages) > 1:
                #Calculate the order - currently unneccesary as only linear is used
                order = min(1, len(self.ch4Percentages) - 1)
                #Convert to polynomial object
                pObject = numpy.polynomial.Polynomial.fit(self.ch4Values, self.ch4Percentages, order)
                #Store regression - coefficient values from fit
                self.ch4Regression = pObject.convert().coef
                #Reverse values
                self.ch4Regression = self.ch4Regression[::-1]
                #Round to 4 decimal places
                for i in range(0, len(self.ch4Regression)):
                    self.ch4Regression[i] = round(self.ch4Regression[i], 4)
                #Generate set of plot points so it can be displayed on the graph
                self.ch4PlotPoints = [[],[]]
                for i in range(min(self.ch4Values), max(self.ch4Values) + 1):
                    value = pObject(i)
                    self.ch4PlotPoints[0].append(i)
                    self.ch4PlotPoints[1].append(value)
        else:
            #If there is more than one carbon dioxide point
            if len(self.co2Percentages) > 1:
                #Calculate the order - currently unneccesary as only linear is used
                order = min(1, len(self.co2Percentages) - 1)
                #Convert to polynomial object
                pObject = numpy.polynomial.Polynomial.fit(self.co2Values, self.co2Percentages, order)
                #Store regression - coefficient values from fit
                self.co2Regression = pObject.convert().coef
                #Reverse values
                self.co2Regression = self.co2Regression[::-1]
                #Round to 4 decimal places
                for i in range(0, len(self.co2Regression)):
                    self.co2Regression[i] = round(self.co2Regression[i], 4)
                #Generate set of plot points so it can be displayed on the graph
                self.co2PlotPoints = [[],[]]
                for i in range(min(self.co2Values), max(self.co2Values) + 1):
                    value = pObject(i)
                    self.co2PlotPoints[0].append(i)
                    self.co2PlotPoints[1].append(value)

    def addCustomMethane(self) -> None:
        '''Allow the user to enter their own data point for methane calibration'''
        #Ask the user for the x value (millivolts as an integer)
        xPoint = simpledialog.askinteger(title="Enter Millivolt Value", prompt="Enter x axis value", initialvalue=0)
        if type(xPoint) == int: 
            #Ask the user for the percentage value (integer)
            yPoint = simpledialog.askinteger(title="Enter Percentage Value", prompt="Enter y axis value", initialvalue=0)
            if type(yPoint) == int:
                #Add point to stored values and update polynomial best fits
                self.ch4Percentages.append(yPoint)
                self.ch4Values.append(xPoint)
                self.calculatePolynomials()
                #Redraw the methane calibration plot
                self.ch4CalPlot.clear()
                for i in range(0, len(self.ch4Values)):
                    if i < len(self.ch4Percentages):
                        self.ch4CalPlot.scatter(self.ch4Values[i], self.ch4Percentages[i], c="blue")
                self.ch4CalPlot.set_title("Methane Calibration")
                #If there is a suitable regression - display it too
                if len(self.ch4Percentages) > 1:
                    self.ch4CalPlot.plot(self.ch4PlotPoints[0], self.ch4PlotPoints[1], c="red")
                self.ch4CalCanvas.draw()
    
    def addCustomCarbonDioxide(self) -> None:
        xPoint = simpledialog.askinteger(title="Enter Millivolt Value", prompt="Enter x axis value", initialvalue=0)
        if type(xPoint) == int:
            yPoint = simpledialog.askinteger(title="Enter Percentage Value", prompt="Enter y axis value", initialvalue=0)
            if type(yPoint) == int:
                self.co2Percentages.append(yPoint)
                self.co2Values.append(xPoint)
                self.calculatePolynomials()
                self.co2CalPlot.clear()
                for i in range(0, len(self.co2Values)):
                    if i < len(self.co2Percentages):
                        self.co2CalPlot.scatter(self.co2Values[i], self.co2Percentages[i], c="blue")
                self.co2CalPlot.set_title("Carbon Dioxide Calibration")
                if len(self.co2Percentages) > 1:
                    self.co2CalPlot.plot(self.co2PlotPoints[0], self.co2PlotPoints[1], c="red")
                self.co2CalCanvas.draw()

    def openCalculation(self, methane) -> None:
        '''Open the calculations window with the correct values and heading'''
        if not self.awaiting:
            #Clear the temporary labels, if they exist
            for label in self.tempLabels:
                label.destroy()
            self.tempLabels = []
            #If displaying carbon dioxide
            if methane:
                #Set correct title
                self.calculationsWindowHeader.configure(text="Methane Calculations")
                regressionUsed = False
                #Iterate through coefficients for the polynomial
                for i in range(0, 4):
                    #If there is a value in the regression to enter
                    if len(self.ch4Regression) > i:
                        self.calValues[i].set(str(self.ch4Regression[-(i + 1)]))
                        regressionUsed = True
                    else:
                        #If the regression is not present and there is a calibration from the device
                        if self.calibrationUpdated and not regressionUsed:
                            #Use value given by device
                            self.calValues[i].set(self.storedCalibration[0][i])
                        else:
                            #Use a 0 for the value
                            self.calValues[i].set("0.0")
                #Iterate through points
                for i in range(0, len(self.ch4Percentages)):
                    if i < len(self.ch4Values):
                        #Create label to display value
                        item = tkinter.Frame(self.calculationsWindow)
                        label = tkinter.Label(item, font=self.fonts["small"], text="{0}% : {1}".format(self.ch4Percentages[i], self.ch4Values[i]))
                        label.pack(side="left", anchor="center", expand=True, fill=None, padx=5)
                        deleteButton = tkinter.Button(item, image=self.smallCrossIcon, command=lambda x=i:self.deletePoint(True, x))
                        deleteButton.pack(side="left", anchor="center", expand=True, fill=None, padx=5)
                        item.grid(row=i + 3, column=0, columnspan=9, sticky="NESW")
                        self.tempLabels.append(item)
            #Displaying methane
            else:
                #Set the correct title
                self.calculationsWindowHeader.configure(text="Carbon Dioxide Calculations")
                regressionUsed = False
                #Iterate through coefficients for the polynomial
                for i in range(0, 4):
                    #If there is a value in the regression to enter
                    if len(self.co2Regression) > i:
                        self.calValues[i].set(str(self.co2Regression[-(i + 1)]))
                        regressionUsed = True
                    else:
                        #If the regression is not present and there is a calibration from the device
                        if self.calibrationUpdated and not regressionUsed:
                            #Use value given by device
                            self.calValues[i].set(self.storedCalibration[1][i])
                        else:
                            #Use a 0 for the value
                            self.calValues[i].set("0.0")
                #Iterate through points
                for i in range(0, len(self.co2Percentages)):
                    if i < len(self.co2Values):
                        #Create label to display value
                        item = tkinter.Frame(self.calculationsWindow)
                        label = tkinter.Label(item, font=self.fonts["small"], text="{0}% : {1}".format(self.co2Percentages[i], self.co2Values[i]))
                        label.pack(side="left", anchor="center", expand=True, fill=None, padx=5)
                        deleteButton = tkinter.Button(item, image=self.smallCrossIcon, command=lambda x=i:self.deletePoint(False, x))
                        deleteButton.pack(side="left", anchor="center", fill=None, padx=5)
                        item.grid(row=i + 3, column=0, columnspan=9, sticky="NESW")
                        self.tempLabels.append(item)
            
            #Store which of the windows is being accessed
            self.methaneOpen = methane
            self.carbonDioxideOpen = not methane
            
            #Display the calculations window
            self.calculationsWindow.deiconify()

    def deletePoint(self, methane : bool, index : int):
        if methane and index > -1 and index < len(self.ch4Percentages) and index < len(self.ch4Values):
            del self.ch4Percentages[index]
            del self.ch4Values[index]
            self.closeCalculations()
            self.calculatePolynomials(True)
            self.updateGraph(True)
        elif (not methane) and index > -1 and index < len(self.co2Percentages) and index < len(self.co2Values):
            del self.co2Percentages[index]
            del self.co2Values[index]
            self.closeCalculations()
            self.calculatePolynomials(False)
            self.updateGraph(False)

    def closeCalculations(self) -> None:
        '''Hide the calculations window and reset which one is open'''
        self.calculationsWindow.withdraw()
        self.methaneOpen = False
        self.carbonDioxideOpen = False

    def sendCalculationPressed(self) -> None:
        '''When button is pressed to send the calibration to the device'''
        #As long as at least one of the windows is open
        if self.methaneOpen or self.carbonDioxideOpen:
            #Store the entered values
            values = [0, 0, 0, 0, 0]
            success = False
            try:
                #Convert entered values to floats
                values = [float(self.calValues[0].get()), float(self.calValues[1].get()), float(self.calValues[2].get()), float(self.calValues[3].get())]
                success = True
            except:
                self.displayMessage("Calibration Set Failed", "Please make sure all entered values are valid numbers and try again.")

            #If values were converted successfully
            if success:
                stringValues = []
                #Iterate through coefficients
                for value in values:
                    #If the string version is short enough
                    if len(str(value)) <= 10:
                        #Add it to the list
                        stringValues.append(str(value))
                    else:
                        #Find length of integer part
                        integerLength = len(str(int(value)))
                        #Find number of decimal places left available
                        floatLength = 10 - integerLength
                        #If the value is negative - value cannot be stored, send None instead
                        if floatLength < 0:
                            stringValues.append(None)
                        else:
                            #Round to the correct number of decimal places
                            stringValues.append(str(round(value, floatLength)))

                if None in stringValues:
                    #Could not send values, too long
                    self.displayMessage("Calibration Set Failed", "Values are too long, maximum ten digits per value.")
                else:
                    gasType = ""
                    #Store a string for the type of gas being set
                    if self.methaneOpen:
                        gasType = "ch4"
                    elif self.carbonDioxideOpen:
                        gasType = "co2"
                    
                    #Construct the message and send it
                    message = "set{0}cal {1}|{2} {3}|{4}\n".format(gasType, stringValues[0], stringValues[1], stringValues[2], stringValues[3])
                    self.sendMessage(message)
                    self.awaiting = True
                    self.calibrationUpdated = False
    
    def updateTimingPressed(self) -> None:
        '''When the update timings button is pressed'''
        #If there is a connected device and not doing something else
        if self.connected and self.calibrating and not self.awaiting:
            #Get the values from the entries
            enteredOpen = self.openTimeEntry.get()
            enteredFlush = self.flushTimeEntry.get()
            allowed = True
            #Convert to integers
            try:
                enteredOpen = int(enteredOpen)
                enteredFlush = int(enteredFlush)
            except:
                #If not possible - cannot set timings
                self.displayMessage("Invalid Values", "Please only enter positive integers.")
                allowed = False
            if allowed:
                #Check that open is at most 9 hours and flush is at most 1 hour
                if enteredOpen < 0 or enteredOpen > 9 * 3600:
                    allowed = False
                    self.displayMessage("Invalid Open Time", "Open time must be more than 0 and less than 9 hours ({0} seconds).".format(9 * 3600))
                if enteredFlush < 0 or enteredFlush > 3600:
                    allowed = False
                    self.displayMessage("Invalid Flush Time", "Flush time must be more than 0 and less than 1 hour (3600 seconds).")
                #Convert to milliseconds
                enteredOpen = enteredOpen * 1000
                enteredFlush = enteredFlush * 1000
            #If there was nothing wrong with the data entered
            if allowed:
                self.awaiting = True
                #Send a message to set the timing information
                self.sendMessage("timingset {0} {1}\n".format(enteredOpen, enteredFlush))
                #Send message to get the timing information
                self.sendMessage("timingget\n")

    def openGraph(self, channel : int, methane : bool) -> None:
        '''Open the graph for the peak values for a given channel'''
        #If it is a valid channel
        if channel > -1 and channel < 16:
            xData = []
            yData = []
            #Take the data for the appropriate gas and add its information to the axes, should they exist
            if methane:
                if len(self.ch4DebugData[channel]) > 0:
                    for i in range(0, len(self.ch4DebugData[channel])):
                        xData.append(i)
                        yData.append(self.ch4DebugData[channel][i])
            else:
                if len(self.co2DebugData[channel]) > 0:
                    for i in range(0, len(self.co2DebugData[channel])):
                        xData.append(i)
                        yData.append(self.co2DebugData[channel][i])
            
            #If there was data
            if len(xData) > 0 and len(yData) > 0:
                #Clear the plot, set titles and add the points
                self.debugPlot.clear()
                if methane:
                    self.debugPlot.set_title("Methane")
                else:
                    self.debugPlot.set_title("Carbon Dioxide")
                self.graphWindowHeaderLabel.configure(text = "Channel {0} Data Points".format(channel + 1))
                self.debugPlot.plot(xData, yData, "-o")
                self.debugCanvas.draw()
                #Display the window
                self.graphWindow.deiconify()
    
    def closeGraph(self) -> None:
        '''Close the debug graphs window'''
        self.graphWindow.withdraw()

    def updateServiceDisplays(self) -> None:
        """Update the in service status of the ui elements"""
        #Iterate through for all the channels there are valid objects for
        for index in range(0, min(len(self.enabledButtons), len(self.currentService), len(self.percentageViews))):
            #If currently being used
            if self.currentService[index]:
                #Set the button to enabled and set the colours of the view window to normal
                self.enabledButtons[index].configure(text="Enabled", bg=self.selectedButtonColour)
                for child in self.percentageViews[index]["frame"].winfo_children():
                    child.configure(bg=self.defaultButtonColour)
                self.percentageViews[index]["frame"].configure(bg=self.defaultButtonColour)
            else:
                #Set the button to disabled and set the colours of the view window to darkened
                self.enabledButtons[index].configure(text="Disabled", bg=self.redTextColour)
                for child in self.percentageViews[index]["frame"].winfo_children():
                    child.configure(bg=self.darkenedColour)
                self.percentageViews[index]["frame"].configure(bg=self.darkenedColour)

    def toggleServicePressed(self, channel) -> None:
        '''When a service toggle button is pressed'''
        #Invert the service state
        self.currentService[channel] = not self.currentService[channel]
        #Send the change to the connected device
        self.updateService()

    def updateService(self) -> None:
        '''When the button is pressed to send the new channel service configuration to the device'''
        #If there is a connected device and not doing something else
        if self.connected and self.calibrating and not self.awaiting:
            self.awaiting = True
            serviceData = ""
            #Iterate through and collect information about the in service state of each channel
            for i in range(0, 15):
                if self.currentService[i]:
                    serviceData = serviceData + "1"
                else:
                    serviceData = serviceData + "0"
            #Send data to device
            self.sendMessage("serviceset {0}\n".format(serviceData))

    def updateValveLabel(self) -> None:
        '''Change the valve label to display which valve is currently open'''
        current = -1
        #Iterate through to find the open valve
        for i in range(0, len(self.valveStates)):
            if self.valveStates[i]:
                current = i
        self.currentValve = current
        #If the valve window is visible at the moment - update it
        if self.valveWindowOpen:
            self.updateValveWindow()

    def updateValveInfoButton(self) -> None:
        """Update the button to display the time remaining on the current action"""
        #Repeat forever while there is a connection
        while self.connected and self.serialConnection != None:
            #Only while on the view screen
            if self.currentMain == 1:
                #Calculate time since the last event
                elapsed = time.time() - self.lastEvent
                #Valve open - reading data
                if self.currentValve > -1 and self.currentValve < 15:
                    remaining = max(int(self.currentOpen - elapsed), 0)
                    self.currentTimeInfoButton.configure(text="Currently Reading Valve {0}, {1} remaining".format(self.currentValve + 1, self.formatSeconds(remaining)))
                #Flushing
                elif self.currentValve == 15:
                    remaining = max(int(self.currentFlush - elapsed), 0)
                    self.currentTimeInfoButton.configure(text="Currently Flushing Via Valve 16, {0} remaining".format(self.formatSeconds(remaining)))
                #All valves closed
                else:
                    self.currentTimeInfoButton.configure(text="Currently Closed")
            #Delay before next check
            time.sleep(0.05)
    
    def formatSeconds(self, seconds : int) -> str:
        """Convert from integer to string and split into seconds, minutes and hours as appropriate"""
        #Seconds only
        if seconds < 60:
            return "{0}s".format(seconds)
        #Seconds and minutes
        if seconds < 60 * 60:
            minutes = seconds // 60
            seconds = seconds - (minutes * 60)
            return "{1}m {2}s".format(minutes, seconds)
        #Seconds minutes and hours
        else:
            hours = seconds // (60 * 60)
            seconds = seconds - (hours * 60 * 60)
            minutes = seconds // 60
            seconds = seconds - (minutes * 60)
            return "{0}h {1}m {2}s".format(hours, minutes, seconds)

    def openValveWindow(self) -> None:
        """Display the window for the valve display"""
        self.updateValveWindow()
        self.valveWindowOpen = True
        self.valveWindow.deiconify()

    def closeValveWindow(self) -> None:
        """Hide the window for the valve display"""
        self.valveWindowOpen = False
        self.valveWindow.withdraw()

    def updateValveWindow(self) -> None:
        """Redraw the canvas on the valve window"""
        #Clear previous drawings
        self.valveCanvas.delete("all")
        #Store center position and valve size
        center = [150, 150]
        circSize = [20, 20]
        current = -1
        #Iterate through to find the open valve
        for i in range(0, len(self.valveStates)):
            if self.valveStates[i]:
                current = i
        #Draw central circle
        self.valveCanvas.create_oval(center[0] - (circSize[0] / 2), center[1] - (circSize[1] / 2), center[0] + (circSize[0] / 2), center[1] + (circSize[1] / 2))
        #Write correct text to show connected valve
        if current != -1:
            if current == 15:
               self.valveCanvas.create_text(center[0], center[1], text="F")
            else: 
                self.valveCanvas.create_text(center[0], center[1], text=str(current + 1))
        else:
            self.valveCanvas.create_text(center[0], center[1], text="-")
        #Radius of inner circle
        radiusSmall = 70
        #Radius of outer circle
        radiusLarge = 90
        #Calculate angle between one value and the next
        radiansBetween = 2 * math.pi / 16
        #Rotate starting point so bottom is 1
        rotation = 2 * math.pi / 4 
        #For both circles
        for r in [radiusSmall, radiusLarge]:
            #For each valve
            for i in range(0, 16):
                #Calculate position for valve
                x = r * math.cos(i * radiansBetween + rotation) + center[0]
                y = r * math.sin(i * radiansBetween + rotation) + center[1]
                #If it is the outer circle or not the current valve
                if r != radiusSmall or current != i:
                    #Draw the circle for the valve
                    self.valveCanvas.create_oval(x - (circSize[0] / 2), y - (circSize[1] / 2), x + (circSize[0] / 2), y + (circSize[1] / 2))
                else:
                    #Draw the circle for the valve but green to indicate an open valve
                    self.valveCanvas.create_oval(x - (circSize[0] / 2), y - (circSize[1] / 2), x + (circSize[0] / 2), y + (circSize[1] / 2), fill="#00AA00")
                #If it is the inner circle or not the current valve
                if r != radiusLarge or current != i: 
                    #Add the number label for the valve
                    #If it is the flush
                    if i == 15:
                        self.valveCanvas.create_text(x, y, text="F")
                    else:
                        self.valveCanvas.create_text(x, y, text=str(i + 1))
                else:
                    #Valve is not currently connected
                    self.valveCanvas.create_text(x, y, text="-")

        #Rectangle to represent body of chimera
        self.valveCanvas.create_rectangle(10, 10, 290, 301)
        #Circle to represent manifold
        self.valveCanvas.create_oval(center[0] - 110, center[1] - 110, center[0] + 110, center[1] + 110)
        #Rectangle to represent sensors
        self.valveCanvas.create_rectangle(25, 275, 275, 300, fill="blue")
    
    def changeSeparators(self, commaChosen) -> None:
        """Update the selected value for the separators"""
        #Default values none selected
        commaColour = self.defaultColour
        commaText = "Choose"
        commaState = "normal"
        semiColour = self.defaultColour
        semiText = "Choose"
        semiState = "normal"
        #Change the one that was selected to highlighted
        if commaChosen:
            commaColour = self.selectedColour
            commaText = "Selected"
            commaState = "disabled"
        else:
            semiColour = self.selectedColour
            semiText = "Selected"
            semiState = "disabled"
        
        #Configure the widgets to display correctly
        self.commaTitle.configure(bg=commaColour)
        self.commaText.configure(bg=commaColour)
        self.commaButton.configure(text=commaText, state=commaState)
        self.commaFrame.configure(bg=commaColour)
        self.semiTitle.configure(bg=semiColour)
        self.semiText.configure(bg=semiColour)
        self.semiButton.configure(text=semiText, state=semiState)
        self.semiFrame.configure(bg=semiColour)

        #If this is different from the saved values - update them
        if commaChosen != self.comma:
            self.comma = commaChosen
            self.saveSeparators()

    def openSeparators(self) -> None:
        """Open the separators window"""
        #If not currently doing something else
        if not self.awaiting:
            #Update to the correct choice
            self.changeSeparators(self.comma)
            #Display window
            self.separatorWindow.deiconify()

    def closeSeparators(self) -> None:
        """Hide the separators window"""
        self.separatorWindow.withdraw()

    def loadSeparators(self) -> None:
        """Attempt to load the separators from the file"""
        try:
            #Path to the separators
            basePath = os.path.expanduser("~")
            basePath = os.path.join(basePath, "AppData", "Local", "AnaeroChimera")
            filePath = os.path.join(basePath, "options.txt")
            #Open file - will fail if not saved before
            settingsFile = open(filePath, "r")
            #Load text
            data = settingsFile.read()
            #Close the file
            settingsFile.close()
            #If there are at least two characters
            if len(data) >= 2:
                #Get first two characters
                part = data[:2]
                #If it is semicolon or not
                if part == "sc":
                    self.comma = False
                else:
                    self.comma = True
            else:
                #Default to comma
                self.comma = True
                #Save the configuration so it is correct next time
                self.saveSeparators()
        except:
            #Default to comma
            self.comma = True
            #Save the configuration so it is correct next time
            self.saveSeparators()

    def saveSeparators(self) -> None:
        """Write the chosen separators to file"""
        #Get the file path
        basePath = os.path.expanduser("~")
        basePath = os.path.join(basePath, "AppData", "Local", "AnaeroChimera")
        #Create the files if they don't already exist
        pathlib.Path(basePath).mkdir(parents=True, exist_ok=True)
        #Open the file
        settingsFile = open(os.path.join(basePath, "options.txt"), "w")
        #Write the correct version to the file
        if self.comma:
            settingsFile.write("cf")
        else:
            settingsFile.write("sc")
        #Close the file
        settingsFile.close()

    def closeFileView(self) -> None:
        """Switch back to the view window from the file view window"""
        if not self.awaiting and not self.downloading:
            #Move frame and clear files
            self.changeMainFrame(1)
            self.setdownFiles()

    def setupFiles(self, fileNames : list, first = False) -> None:
        '''Set up the scrollable button section of each file given a list of file names'''
        if self.filesOpen:
            self.setdownFiles()
        self.filesOpen = True
        #Create canvas and scroll bar
        self.fileCanvas = tkinter.Canvas(self.fileListFrame, bg=self.defaultButtonColour)
        self.fileScroll = tkinter.Scrollbar(self.fileListFrame, orient="vertical", command=self.fileCanvas.yview)

        #Add canvas and scroll bar to the frame
        self.fileScroll.pack(side="right", fill="y")
        self.fileCanvas.pack(side="left", expand=True, fill="both")

        #Create grid to hold the buttons
        self.fileGridFrame = tkinter.Frame(self.fileCanvas)
        
        #Configure the grid on the frame so it has the correct weighting and size for each file (1 column and as many rows as files)
        self.fileGridFrame.grid_columnconfigure(0, weight=1)
        for row in range(0, len(fileNames)):
            self.fileGridFrame.grid_rowconfigure(row, minsize=70)
        
        #Reset list that will store the buttons references
        self.fileButtons = []

        #Iterate through the file names
        for nameId in range(0, len(fileNames)):
            sizePart = ""
            if len(self.fileSizes) > nameId and self.fileSizes[nameId] != -1:
                size = self.fileSizes[nameId]
                if size / 1000000 > 1:
                    sizePart = str(int(size / 1000000)) + "MB"
                elif size / 1000 > 1:
                    sizePart = str(int(size / 1000)) + "KB"
                else:
                    sizePart = str(size) + "B"
            fontColour = self.blackTextColour
            if fileNames[nameId] == self.currentTimeFileName:
                fontColour = self.blueTextColour
            #Create a button and add it to the list
            button = tkinter.Button(self.fileGridFrame, text=fileNames[nameId] + "   " + sizePart, relief="groove", command=lambda x=nameId: self.filePressed(x), font=self.fonts["medium"], fg=fontColour)
            #If this is the file currently being used
            if fileNames[nameId] == self.currentFileName:
                #Display it's name in blue
                button.configure(fg = self.blueTextColour)
            button.grid(row=nameId, column=0, sticky="NESW")
            self.fileButtons.append(button)

        #Create a window in the canvas to display the frame of buttons
        self.fileCanvasWindow = self.fileCanvas.create_window(0, 0, window=self.fileGridFrame, anchor="nw")

        #Setup the resizing commands on the canvas and frame
        self.fileGridFrame.bind("<Configure>", self.onFrameConfigure)
        self.fileCanvas.bind("<Configure>", self.frameWidth)
        self.frameWidth(None)

        #Update the initial size on the canvas (so it looks correct on first load)
        self.fileCanvas.update_idletasks()

        #Add enter and leave mousewheel binding so it can be scrolled
        self.fileGridFrame.bind("<Enter>", self.bindMouseWheel)
        self.fileGridFrame.bind("<Leave>", self.unbindMouseWheel)
        
        #Setup bounding box and scroll region so the scrolling works correctly
        self.fileCanvas.configure(scrollregion=self.fileCanvas.bbox("all"), yscrollcommand=self.fileScroll.set)
    
    def setdownFiles(self) -> None:
        '''Remove all file buttons from scroll section'''
        if self.filesOpen:
            #If there is currently a selected file
            if self.selectedFile != -1:
                #Deselect the file
                self.filePressed(self.selectedFile)

            #Delete the canvas and scroll bar
            self.fileCanvas.destroy()
            self.fileScroll.destroy()

            #Reset all variables holding information about the section
            self.fileCanvas = None
            self.fileScroll = None
            self.fileGridFrame = None
            self.fileButtons = []
            self.fileCanvasWindow = None

            self.filesOpen = False
            #self.openFilesButton.configure(text="Open Files")
            self.downloadFileButton.configure(state="disabled")
            self.deleteFileButton.configure(state="disabled")
            self.files = []

            self.filesOpen = False

    def setupProgressBar(self, maxValue: int) -> None:
        '''Configure the progress bar and place it into the UI'''
        #Set its maximum value
        self.progressBar.configure(maximum = maxValue)
        #Store the number that will be downloaded (for calculating percentages)
        self.charactersToDownload = maxValue
        #Set the value and text to 0 downloaded
        self.progressBar["value"] = 0
        self.styles.configure("ProgressbarLabeled", text="Downloading...00%")
        #Place progress bar into UI
        self.progressBar.grid()
        #Create a separate thread to control the progress bar
        progressThread = Thread(target=self.updateProgressBar, daemon=True)
        #Start the progress bar thread
        progressThread.start()

    def updateProgressBar(self) -> None:
        '''Update the value currently being shown by the progress bar'''
        value = self.downloadedCharacters
        #Set the value
        self.progressBar["value"] = value
        #If the download is done
        if value >= self.charactersToDownload:
            #Display that the download is complete
            self.styles.configure("ProgressbarLabeled", text="Download Complete")
        else:
            #Calculate the percentage downloaded and convert to string
            percentage = str(int((value / self.charactersToDownload) * 100))
            #If it has less than 2 digits
            if len(percentage) < 2:
                #Add a leading zero
                percentage = "0" + percentage
            #Display the percentage downloaded
            self.styles.configure("ProgressbarLabeled", text="Downloading..." + percentage + "%")
            #Repeat this after 10 ms
            self.after(10, self.updateProgressBar)

    def setdownProgressBar(self) -> None:
        '''Remove the progress bar from the UI and reset it'''
        self.progressBar.grid_remove()
        self.progressBar["value"] = 0
        self.styles.configure("ProgressbarLabeled", text="Downloading...00%")

    def onFrameConfigure(self, event) -> None:
        '''Event called when canvas frame resized'''
        #Update canvas bounding box
        self.fileCanvas.configure(scrollregion=self.fileCanvas.bbox("all"))

    def frameWidth(self, event) -> None:
        '''Event called when canvas resized'''
        #canvasWidth = event.width
        canvasWidth = self.fileCanvas.winfo_width()
        #Update size of window on canvas
        self.fileCanvas.itemconfig(self.fileCanvasWindow, width=canvasWidth - 1)

    def bindMouseWheel(self, event) -> None:
        '''Add mouse wheel binding to canvas'''
        if self.fileCanvas != None:
            self.fileCanvas.bind_all("<MouseWheel>", self.mouseWheelMove)

    def unbindMouseWheel(self, event) -> None:
        '''Remove mouse wheel binding from canvas'''
        if self.fileCanvas != None:
            self.fileCanvas.unbind_all("<MouseWheel>")

    def mouseWheelMove(self, event) -> None:
        '''Change y scroll position when mouse wheel moved'''
        if self.fileCanvas != None:
            self.fileCanvas.yview_scroll(int(-1 * (event.delta / 120)), "units")

    def closeWindow(self) -> None:
        if not self.awaiting:
            if self.currentMain == 0:
                self.parent.destroy()
            elif self.currentMain == 1:
                if self.connected and self.serialConnection != None:
                    self.disconnect()
                else:
                    self.parent.destroy()
            elif self.currentMain == 2:
                self.endConfigurePressed()
            elif self.currentMain == 3:
                self.closeFileView()

#Only run if this is the main module being run
if __name__ == "__main__":
    #Create root window for tkinter
    root = tkinter.Tk()
    #Set the shape of the window
    root.geometry("900x760")
    root.minsize(900, 760)
    #Allow for expanding sizes
    root.grid_rowconfigure(0, weight=1)
    root.grid_columnconfigure(0, weight=1)
    #Set the title text of the window
    root.title("Chimera Client")
    #Add the editor to the root windows
    window = MainWindow(root)
    window.grid(row = 0, column=0, sticky="NESW")
    ico = Image.open(window.pathTo("images/icon.png"))
    photo = ImageTk.PhotoImage(ico)
    root.wm_iconphoto(True, photo)
    #If the window is attempted to be closed, call the close window function
    root.protocol("WM_DELETE_WINDOW", window.closeWindow)
    #Start running the root
    root.mainloop()
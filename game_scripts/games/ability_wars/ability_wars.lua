local Rayfield = loadstring(game:HttpGet("https://sirius.menu/rayfield"))()

local theme = {
    TextColor = Color3.fromRGB(245, 230, 230),

    Background = Color3.fromRGB(20, 10, 10),
    Topbar = Color3.fromRGB(30, 15, 15),
    Shadow = Color3.fromRGB(10, 5, 5),

    NotificationBackground = Color3.fromRGB(26, 14, 14),
    NotificationActionsBackground = Color3.fromRGB(50, 35, 35),

    TabBackground = Color3.fromRGB(36, 20, 20),
    TabStroke = Color3.fromRGB(50, 30, 30),
    TabBackgroundSelected = Color3.fromRGB(72, 36, 36),
    TabTextColor = Color3.fromRGB(210, 170, 170),
    SelectedTabTextColor = Color3.fromRGB(255, 220, 220),

    ElementBackground = Color3.fromRGB(32, 18, 18),
    ElementBackgroundHover = Color3.fromRGB(42, 24, 24),
    SecondaryElementBackground = Color3.fromRGB(26, 16, 16),
    ElementStroke = Color3.fromRGB(70, 40, 40),
    SecondaryElementStroke = Color3.fromRGB(55, 35, 35),

    SliderBackground = Color3.fromRGB(140, 70, 70),
    SliderProgress = Color3.fromRGB(220, 100, 100),
    SliderStroke = Color3.fromRGB(255, 120, 120),

    ToggleBackground = Color3.fromRGB(32, 20, 20),
    ToggleEnabled = Color3.fromRGB(220, 100, 100),
    ToggleDisabled = Color3.fromRGB(100, 100, 100),
    ToggleEnabledStroke = Color3.fromRGB(255, 130, 130),
    ToggleDisabledStroke = Color3.fromRGB(70, 70, 70),
    ToggleEnabledOuterStroke = Color3.fromRGB(255, 150, 150),
    ToggleDisabledOuterStroke = Color3.fromRGB(50, 50, 50),

    DropdownSelected = Color3.fromRGB(40, 25, 25),
    DropdownUnselected = Color3.fromRGB(32, 20, 20),

    InputBackground = Color3.fromRGB(30, 18, 18),
    InputStroke = Color3.fromRGB(70, 50, 50),
    PlaceholderColor = Color3.fromRGB(210, 180, 180)
}

local Window = Rayfield:CreateWindow({
   Name = "exception.red",
   Icon = nil,
   LoadingTitle = "exception.red",
   LoadingSubtitle = "loading...",
   Theme = theme,

   ToggleUIKeybind = "K",

   DisableRayfieldPrompts = true,
   DisableBuildWarnings = true,

   ConfigurationSaving = {
      Enabled = false,
      FolderName = nil,
      FileName = "exception.red"
   }
})

local visuals_tab = Window:CreateTab("Visuals", "scan-eye")
local combat_tab = Window:CreateTab("Combat", "swords")
local client_tab = Window:CreateTab("Client", "computer")
local utility_tab = Window:CreateTab("Utility", "hammer")
local user_tab = Window:CreateTab("User", "square-user-round")

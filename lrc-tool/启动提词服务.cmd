@echo off
chcp 936 >nul
setlocal
title 歌词配轴 · 提词服务
set "PY=C:\Users\whx\AppData\Local\DoubaoWork\User Data\sandbox_runtime\bases\fa694f517e5995233c80a9a8db5212c2\python\python.exe"
if not exist "%PY%" (
  for /f "delims=" %%P in ('where python 2^>nul') do if not defined PYA set "PYA=%%P"
  if defined PYA set "PY=%PYA%"
)
if not exist "%PY%" (
  echo 找不到 Python 环境，先把豆包工作打开一次再试。
  pause
  exit /b 1
)
if not exist "%~dp0提词服务.py" (
  echo 找不到 提词服务.py，请保持它和本窗口在同一目录。
  pause
  exit /b 1
)
echo 正在启动提词服务，浏览器会自动打开工具页面...
echo 这个窗口不要关，关掉就停止服务。
echo.
"%PY%" "%~dp0提词服务.py" --open
echo.
echo 服务已停止。
pause

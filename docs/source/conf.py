# Configuration file for the Sphinx documentation builder.
#
# For the full list of built-in configuration values, see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html
# -- Project information -----------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#project-information
project = 'mathlib probability study note'
copyright = '2025, Kei Tsukamoto'
author = 'Kei Tsukamoto'
# -- General configuration ---------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#general-configuration

# 拡張機能リストを一箇所にまとめる
extensions = [
    'sphinx.ext.autodoc',
    'sphinx.ext.viewcode',
    'sphinx.ext.napoleon',
    'sphinx.ext.mathjax',
    'myst_parser'
]

# MyST-Parser settings
myst_enable_extensions = [
    "dollarmath",       # インライン数式とディスプレイ数式のサポート
    "amsmath",          # AMSマス環境のサポート
    "colon_fence",      # :::コロン区切りの特殊ブロック
    "deflist",          # 定義リスト
    "html_image",       # HTML画像構文
]

# マークダウンファイルの拡張子を指定
source_suffix = {
    '.rst': 'restructuredtext',
    '.md': 'markdown',
}

templates_path = ['_templates']
exclude_patterns = []
# -- Options for HTML output -------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#options-for-html-output
# Theme settings
html_theme = 'sphinx_rtd_theme' # Or any other theme you prefer

# Output settings for GitHub Pages
html_static_path = ['_static']
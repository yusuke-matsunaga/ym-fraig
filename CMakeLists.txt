
# ===================================================================
# インクルードパスの設定
# ===================================================================
include_directories (
  ${PROJECT_BINARY_DIR}/include
  ${PROJECT_SOURCE_DIR}/ym-common/include
  ${PROJECT_SOURCE_DIR}/ym-base/include
  ${PROJECT_SOURCE_DIR}/ym-logic/include
  ${PROJECT_SOURCE_DIR}/ym-sat/include
  ${PROJECT_SOURCE_DIR}/ym-cell/include
  ${PROJECT_SOURCE_DIR}/ym-bnet/include
  ${CMAKE_CURRENT_SOURCE_DIR}/include
  )


# ===================================================================
# サブディレクトリの設定
# ===================================================================

add_subdirectory ( c++-test )
#add_subdirectory ( py-test )

# ===================================================================
#  ソースファイルの設定
# ===================================================================

set ( fraig_SOURCES
  c++-src/FraigMgr.cc
  c++-src/FraigMgrImpl.cc
  c++-src/FraigHandle.cc
  c++-src/FraigHash.cc
  c++-src/FraigNode.cc
  c++-src/PatHash.cc
  c++-src/StructHash.cc
  )


# ===================================================================
# ターゲットの設定
# ===================================================================

ym_add_object_library ( ym_fraig
  ${fraig_SOURCES}
  )

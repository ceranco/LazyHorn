set (EXT_LIBRARIES ${Z3_LIBRARY})

add_executable(ih main.cpp Stats.cpp Global.cpp)

target_link_libraries (ih ${EXT_LIBRARIES} ${Boost_PROGRAM_OPTIONS_LIBRARY} m dl pthread z  stdc++ ${RT_LIB})

if (IH_STATIC_EXE)
    set (CMAKE_EXE_LINKER_FLAGS "-static -static-libgcc -static-libstdc++")
    set_target_properties (ih PROPERTIES LINK_SEARCH_START_STATIC ON)
    set_target_properties (ih PROPERTIES LINK_SEARCH_END_STATIC ON)
endif()
#add_subdirectory(src)



import React from 'react';
export const PrpeleafEditorGlobalContext = React.createContext({
	readOnly: false,
	changeText: () => {},
});
